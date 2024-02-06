/*
 * Copyright (C) 2021-2022 Max Barth (Max.Barth95@gmx.de)
 * Copyright (C) 2021-2022 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import java.math.BigInteger;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector.IntBlastConstrainer.ConstraintsForBitwiseOperations;

public class IntBlaster extends TermTransformer {
	private final Theory mTheory;
	private static final String BITVEC_CONST_PATTERN = "bv\\d+";

	private final TermVariable[] mFreeVars;
	private final IntBlastConstrainer mTc;

	private final LinkedHashMap<Term, Term> mVariableMap; // Maps BV Var to Integer Var
	private final LinkedHashMap<Term, Term> mReversedVarMap;
	public final LinkedHashMap<Term, Term> mArraySelectConstraintMap;
	private final Set<Term> mOverapproxVariables;
	private boolean mIsOverapproximation;
	private final boolean mLazyModulo = false;

	/*
	 * Translates a formula over bit-vector to a formula over integers. Can
	 * translate arrays and quantifiers.
	 */
	public IntBlaster(final Theory theory, final LinkedHashMap<Term, Term> variableMap, final IntBlastConstrainer tc,
			final TermVariable[] freeVars) {

		mTheory = theory;
		mFreeVars = freeVars;
		if (variableMap != null) {
			mVariableMap = variableMap;
		} else {
			mVariableMap = new LinkedHashMap<>();
		}

		mReversedVarMap = new LinkedHashMap<>();
		mArraySelectConstraintMap = new LinkedHashMap<>();
		mOverapproxVariables = new HashSet<>();
		mIsOverapproximation = false;
		mTc = tc;
	}

	@Override
	public void convert(final Term term) {
		final Sort intSort = mTheory.getNumericSort();
		if (term instanceof TermVariable) {
			for (final TermVariable variable : mFreeVars) {
				if (term == variable && term.getSort().isBitVecSort()) {
					final Term intVar = translateVars(term, true);
					assert (intVar.getSort().isNumericSort());
					// mTc.varConstraint(term, intVar); // Create and Collect Constraints
					mTc.varLaBounds(term, intVar); // TODO
					setResult(intVar);
					return;
				}
			}
			setResult(translateVars(term, true));
			return;
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;

			final FunctionSymbol fsym = appTerm.getFunction();
			if (appTerm.getParameters().length == 0) {
				final Term intVar = translateVars(term, true);
				if (term.getSort().isBitVecSort()) {
					// mTc.varConstraint(term, intVar); // Create and Collect Constraints
					mTc.varLaBounds(term, intVar); // TODO
				}
				setResult(intVar);
				return;
			}
			// NONE Overapproximation
			if (mTc.mMode.equals(ConstraintsForBitwiseOperations.NONE) && overaproxWithVars(appTerm)) {
				final Sort newSort = translateSort(appTerm.getSort());
				final TermVariable overaproxVar = mTheory.createFreshTermVariable("overaproxVar", newSort);
				mOverapproxVariables.add(overaproxVar);
				mIsOverapproximation = true;
				setResult(overaproxVar);
				return;
			}
			if (fsym.isIntern()) {
				switch (fsym.getName()) {
				case "bvor": {
					// bvor = bvsub(bvadd, bvand)
					final Term bvor = mTheory.term("bvsub", mTheory.term("bvadd", appTerm.getParameters()),
							mTheory.term("bvand", appTerm.getParameters()));
					pushTerm(bvor);
					return;
				}
				case "bvxor": {
					pushTerm(mTheory.term("bvsub",
							mTheory.term("bvsub", mTheory.term("bvadd", appTerm.getParameters()),
									mTheory.term("bvand", appTerm.getParameters())),
							mTheory.term("bvand", appTerm.getParameters())));
					return;
				}
				}
			}
		} else if (term instanceof ConstantTerm) {
			if (term.getSort().isBitVecSort()) {
				final ConstantTerm constTerm = (ConstantTerm) term;
				assert isBitVecSort(constTerm.getSort());
				BigInteger constValue;
				if (constTerm.getValue() instanceof String) {
					String bitString = (String) constTerm.getValue();
					if (bitString.startsWith("#b")) {
						bitString = (String) constTerm.getValue();
						constValue = new BigInteger(bitString.substring(2), 2);
					} else if (bitString.startsWith("#x")) {
						constValue = new BigInteger(bitString.substring(2), 16);
					} else {
						throw new UnsupportedOperationException("Unexpected constant type");
					}
				} else {
					constValue = (BigInteger) constTerm.getValue();
				}
				final Term intConst = mTheory.rational(Rational.valueOf(constValue, BigInteger.ONE), intSort);

				setResult(intConst);
				return;
			} else {
				throw new UnsupportedOperationException("unexpected constant sort");
			}
		}
		super.convert(term);

	}

	/*
	 * translate variables and uninterpreted constants of bit-vector sort or array
	 * sort adds bv and int variable to mVariableMap and mReversedVarMap returns the
	 * new variable (translation results)
	 */
	private Term translateVars(final Term term, final boolean addToVarMap) {
		if (mVariableMap.containsKey(term)) {
			mReversedVarMap.put(mVariableMap.get(term), term);
			return mVariableMap.get(term);
		} else {
			final Sort sort = term.getSort();
			if (sort.isBitVecSort()) {
				Term intVar;

				intVar = mTheory.createFreshTermVariable("intVar", mTheory.getNumericSort());

				if (addToVarMap) {
					mVariableMap.put(term, intVar);
					mReversedVarMap.put(intVar, term);
				}
				return intVar;
			} else {
				return term;
			}

		}

	}

	/*
	 * TODO more modular
	 */
	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] args) {
		final Sort intSort = mTheory.getNumericSort();
		final BigInteger two = BigInteger.valueOf(2);
		final FunctionSymbol fsym = appTerm.getFunction();
		if (fsym.isIntern()) {
			switch (fsym.getName()) {
			case "and":
			case "or":
			case "not":
			case "=>":
			case "store":
				assert args.length == 3;
//Todo is mLazyModulo even necessary with bv2nat und nat2bv?
				if (mLazyModulo && appTerm.getParameters()[1].getSort().isBitVecSort()) {
					final int width = Integer.valueOf(appTerm.getParameters()[1].getSort().getIndices()[0]);
					// maximal representable number by a bit-vector of width
					// "width" plus one
					final Term maxNumberPlusOne = mTheory.rational(Rational.valueOf(two.pow(width), BigInteger.ONE),
							intSort);

					final Term mod = mTheory.term("mod", args[1], maxNumberPlusOne);
					setResult(mTheory.term(fsym.getName(), args[0], mod, args[2]));
					return;
				} else {
					setResult(mTheory.term(fsym.getName(), args[0], args[1], args[2]));
					return;
				}
			case "select": {
				// select terms can act to variables
				assert args.length == 2;
				if (appTerm.getSort().isBitVecSort()) {
					Term index;
					if (!mLazyModulo) {
						// select terms can act as variables

						mArraySelectConstraintMap.put(args[0],
								mTc.getSelectConstraint(appTerm, mTheory.term(fsym.getName(), args)));
						index = args[1];
					} else {
						final int width = Integer.valueOf(appTerm.getParameters()[1].getSort().getIndices()[0]);
						// maximal representable number by a bit-vector of width
						// "width" plus one
						final Term maxNumberPlusOne = mTheory.rational(Rational.valueOf(two.pow(width), BigInteger.ONE),
								intSort);
						final Term mod = mTheory.term("mod", args[1], maxNumberPlusOne);
						index = mod;
					}

					setResult(mTheory.term(fsym.getName(), args[0], index));
					return;
				} else {
					setResult(mTheory.term(fsym.getName(), args[0], args[1]));
					return;
				}
			}
			}
		}

		if (appTerm.getParameters().length == 0) {
			if (fsym.getName().matches(BITVEC_CONST_PATTERN)) {
				final BigInteger constValue = new BigInteger(fsym.getName().substring(2));
				final Term intConst = mTheory.rational(Rational.valueOf(constValue, BigInteger.ONE), intSort);

				setResult(intConst);
				return;
			} else if (mTheory.mFalse.equals(appTerm)) {
				setResult(appTerm);
				return;
			} else if (mTheory.mTrue.equals(appTerm)) {
				setResult(appTerm);
				return;
			} else {
				setResult(mVariableMap.get(appTerm));
				return;
			}
		} else if (appTerm.getParameters().length == 1 && appTerm.getParameters()[0].getSort().isBitVecSort()) {
			// width of the first argument
			final int width = Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]);
			// maximal representable number by a bit-vector of width "width" plus one
			final Term maxNumberPlusOne = mTheory.rational(Rational.valueOf(two.pow(width), BigInteger.ONE), intSort);

			final Term translatedLHS = args[0];
			if (fsym.isIntern()) {
				switch (fsym.getName()) {
				case "bvnot": {
					final Term not = mTheory.term("-", maxNumberPlusOne,
							mTheory.term("+", translatedLHS, mTheory.rational(Rational.ONE, intSort)));
					setResult(not);
					return;
				}
				case "bvneg": {
					final Term negation = mTheory.term("-", maxNumberPlusOne, translatedLHS);
					if (mLazyModulo) {
						setResult(negation);
						return;
					}
					setResult(mTheory.term("mod", negation, maxNumberPlusOne));
					return;
				}
				case "extract": {

					setResult(translateExtract(appTerm, translatedLHS));
					return;
				}
				case "zero_extend":
					if (mLazyModulo) {
						final Term maxNumber = mTheory.rational(Rational.valueOf(two.pow(width), BigInteger.ONE),
								intSort);

						setResult(mTheory.term("mod", args[0], maxNumber));
						return;
					}
					setResult(args[0]);
					return;
				case "const":
				case "repeat":
				case "rotate_left":
				case "rotate_right":
				default:
					throw new UnsupportedOperationException("unexpected function: " + fsym.getName());
				}
			}
		} else {
			int width = 0;
			if (appTerm.getParameters()[0].getSort().isBitVecSort()) {
				width = Integer.valueOf(appTerm.getParameters()[1].getSort().getIndices()[0]);
			}
			final Term maxNumber = mTheory.rational(Rational.valueOf(two.pow(width), BigInteger.ONE), intSort);
			final Term[] translatedArgs = args;
			if (fsym.isIntern()) {
				switch (fsym.getName()) {
				case "=":
				case "distinct":
				case "bvult":
				case "bvule":
				case "bvugt":
				case "bvuge":
				case "bvslt":
				case "bvsle":
				case "bvsgt":
				case "bvsge": {
					setResult(translateRelations(fsym, args, maxNumber, width));
					return;
				}
				case "bvadd": {
					final Term addition = mTheory.term("+", translatedArgs);
					// nat2bv(mTheory.term("+", translatedArgs))
					// bvadd(a b) -> nat2bv_k (mTheory.term("+", bv2nat_k(a) bv2nat_k(b) ))

					// bvadd(a bvadd(b c)) -> nat2bv_k (mTheory.term("+", bv2nat_k(a),
					// bv2nat_k(nat2bv_k (mTheory.term("+", bv2nat_k(b) bv2nat_k(c) )))))

					// optimierung nat2bv_k(bv2nat_k) = nix , bv2nat_k(nat2bv_k)

					if (mLazyModulo) {
						setResult(addition);
						return;
					}
					setResult(mTheory.term("mod", addition, maxNumber));
					return;
				}
				case "bvsub": {
					final Term substraction = mTheory.term("-", translatedArgs);
					if (mLazyModulo) {
						setResult(substraction);
						return;
					}
					setResult(mTheory.term("mod", substraction, maxNumber));
					return;
				}
				case "bvmul": {
					final Term multiplication = mTheory.term("*", translatedArgs);
					if (mLazyModulo) {
						setResult(multiplication);
						return;
					}
					setResult(mTheory.term("mod", multiplication, maxNumber));
					return;
				}
				case "ite": {
					setResult(mTheory.term("ite", args[0], args[1], args[2]));
					return;
				}
				}

				if (appTerm.getParameters().length == 2) {
					final Term translatedLHS = translatedArgs[0];
					final Term translatedRHS = translatedArgs[1];
					switch (fsym.getName()) {
					case "bvshl": {
						setResult(translateBvshl(translatedLHS, translatedRHS, width, maxNumber));
						return;
					}
					case "bvlshr": {
						setResult(translateBvlshr(translatedLHS, translatedRHS, width, maxNumber));
						return;
					}

					case "bvashr": {
						throw new UnsupportedOperationException(fsym.getName());
					}
					case "concat": {
						final Term multiplication = mTheory.term("*", translatedLHS, maxNumber);
						if (mLazyModulo) {
							setResult(mTheory.term("+", multiplication, mTheory.term("mod", translatedRHS, maxNumber)));
							return;
						}
						setResult(mTheory.term("+", multiplication, translatedRHS));
						return;
					}

					case "bvudiv": {
						setResult(translateBvudiv(translatedLHS, translatedRHS, maxNumber));
						return;
					}

					case "bvurem": {
						setResult(translateBvurem(translatedLHS, translatedRHS, maxNumber));
						return;
					}
					case "bvand": {
						throw new UnsupportedOperationException(
								"unsupported bitwise operation in Intblasting " + fsym.getName());
//						if (replaceUfIntand) {
//							setResult(mTc.bvandSUMforReplacement(width, translatedLHS, translatedRHS));
//							return;
//						} else {
						// final Term intAnd =
						// mTheory.term(mTc.getIntAndFunctionSymbol().getName(), translatedLHS,
						// translatedRHS);
						// final boolean constraintsOverapproximate = mTc.bvandConstraint(intAnd,
						// width);
						// if (constraintsOverapproximate) {
//						mIsOverapproximation = true;
//					}
						// setResult(intAnd);
						// return;
					}
					default:
						throw new UnsupportedOperationException("unexpected function: " + fsym.getName());

					}
				}
			}

		}
		super.convertApplicationTerm(appTerm, args);
	}

	@Override
	public void postConvertLet(final LetTerm oldLet, final Term[] newValues, final Term newBody) {
		throw new UnsupportedOperationException("Let terms are not yet supported.");
	}

	private Term translateExtract(final ApplicationTerm appTerm, final Term translatedLHS) {
		final Sort intSort = mTheory.getNumericSort();
		final BigInteger two = BigInteger.valueOf(2);
		final int lowerIndex = Integer.parseInt(appTerm.getFunction().getIndices()[1]);
		final int upperIndex = Integer.parseInt(appTerm.getFunction().getIndices()[0]);

		final Term divby = mTheory.rational(Rational.valueOf(two.pow(lowerIndex), BigInteger.ONE), intSort);
		final Term modby = mTheory.rational(Rational.valueOf(two.pow(upperIndex - lowerIndex + 1), BigInteger.ONE),
				intSort);
		return mTheory.term("mod", mTheory.term("div", translatedLHS, divby), modby);
	}

	private Term translateBvudiv(final Term translatedLHS, final Term translatedRHS, final Term maxNumber) {
		final Sort intSort = mTheory.getNumericSort();
		Term rhs;
		Term lhs;

		if (mLazyModulo) {
			rhs = mTheory.term("mod", translatedRHS, maxNumber);
			lhs = mTheory.term("mod", translatedLHS, maxNumber);
		} else {
			rhs = translatedRHS;
			lhs = translatedLHS;
		}

		final Term ifTerm = mTheory.term("=", rhs, mTheory.rational(Rational.ZERO, intSort));
		final Term thenTerm = mTheory.term("-", maxNumber, mTheory.rational(Rational.ONE, intSort));
		final Term elseTerm = mTheory.term("div", lhs, rhs);
		return mTheory.term("ite", ifTerm, thenTerm, elseTerm);
	}

	private Term translateBvurem(final Term translatedLHS, final Term translatedRHS, final Term maxNumber) {
		Term rhs;
		Term lhs;
		final Sort intSort = mTheory.getNumericSort();

		if (mLazyModulo) {
			rhs = mTheory.term("mod", translatedRHS, maxNumber);
			lhs = mTheory.term("mod", translatedLHS, maxNumber);
		} else {
			rhs = translatedRHS;
			lhs = translatedLHS;
		}

		final Term ifTerm = mTheory.term("=", rhs, mTheory.rational(Rational.ZERO, intSort));
		final Term thenTerm = lhs;
		final Term elseTerm = mTheory.term("mod", lhs, rhs);
		return mTheory.term("ite", ifTerm, thenTerm, elseTerm);
	}

	private Term translateBvshl(Term translatedLHS, Term translatedRHS, final int width, final Term maxNumber) {
		final Sort intSort = mTheory.getNumericSort();
		if (mLazyModulo) {
			translatedRHS = mTheory.term("mod", translatedRHS, maxNumber);
			translatedLHS = mTheory.term("mod", translatedLHS, maxNumber);
		}
		if (translatedRHS instanceof ConstantTerm) {
			final Term shift = mTheory.term("*", translatedLHS, pow2(translatedRHS));
			return mTheory.term("mod", shift, maxNumber);
		} else {
			Term iteChain = mTheory.rational(Rational.ZERO, intSort);
			for (int i = width - 1; i >= 0; i--) {
				if (i == 0) {
					final Term constInt = mTheory.rational(Rational.valueOf(0, 1), intSort);
					iteChain = mTheory.term("ite", mTheory.term("=", constInt, translatedRHS), translatedLHS, iteChain);
				} else {
					final Rational powResult = Rational.valueOf(i, 1);
					final Term ifTerm = mTheory.term("=", translatedRHS, mTheory.rational(powResult, intSort));
					final BigInteger pow = BigInteger.valueOf(2).pow(i);
					final Term thenTerm;
					if (mLazyModulo) {
						thenTerm = mTheory.term("*", mTheory.rational(Rational.valueOf(pow, BigInteger.ONE), intSort),
								translatedLHS);
					} else {
						thenTerm = mTheory.term("mod", mTheory.term("*",
								mTheory.rational(Rational.valueOf(pow, BigInteger.ONE), intSort), translatedLHS),
								maxNumber);
					}

					iteChain = mTheory.term("ite", ifTerm, thenTerm, iteChain);
				}
			}
			return iteChain;
		}
	}

	private Term translateBvlshr(Term translatedLHS, Term translatedRHS, final int width, final Term maxNumber) {
		final Sort intSort = mTheory.getNumericSort();
		if (mLazyModulo) {
			translatedRHS = mTheory.term("mod", translatedRHS, maxNumber);
			translatedLHS = mTheory.term("mod", translatedLHS, maxNumber);
		}
		if (translatedRHS instanceof ConstantTerm) {
			final Term shift = mTheory.term("div", translatedLHS, pow2(translatedRHS));
			return shift;
		} else {
			Term iteChain = mTheory.rational(Rational.ZERO, intSort);
			for (int i = width - 1; i >= 0; i--) {
				if (i == 0) {
					final Term constInt = mTheory.rational(Rational.valueOf(0, 1), intSort);
					iteChain = mTheory.term("ite", mTheory.term("=", constInt, translatedRHS), translatedLHS, iteChain);
				} else {
					final Rational powResult = Rational.valueOf(i, 1);
					final Term ifTerm = mTheory.term("=", translatedRHS, mTheory.rational(powResult, intSort));
					final BigInteger pow = BigInteger.valueOf(2).pow(i);
					final Term thenTerm = mTheory.term("div", translatedLHS,
							mTheory.rational(Rational.valueOf(pow, BigInteger.ONE), intSort));
					iteChain = mTheory.term("ite", ifTerm, thenTerm, iteChain);
				}
			}
			return iteChain;
		}
	}

	private Term translateRelations(final FunctionSymbol fsym, final Term[] args, final Term maxNumberPlusOne,
			final int width) {
		Term[] translatedArgs = new Term[args.length];

		translatedArgs = args;

		if (fsym.isIntern()) {
			switch (fsym.getName()) {
			case "=":
			case "distinct":
			case "bvult":
			case "bvule":
			case "bvugt":
			case "bvuge": {
				if (mLazyModulo && args[0].getSort().isBitVecSort()) {
					for (int i = 0; i < args.length; i++) {
						translatedArgs[i] = mTheory.term("mod", args[i], maxNumberPlusOne);
					}
				}
				return mTheory.term(fsym.getName(), translatedArgs);
			}
			case "bvslt":
			case "bvsle":
			case "bvsgt":
			case "bvsge": {
				final Term[] utsArgs = args;
				for (int i = 0; i < args.length; i++) {
					utsArgs[i] = uts(width, args[i], mLazyModulo);
				}
				return (mTheory.term(fsym.getName(), utsArgs));

			}
			}
		}
		throw new UnsupportedOperationException("unexpected relation");
	}

	// unsigned to signed for relations
	private final Term uts(final int width, final Term term, final boolean lazyModulo) {
		// 2 * (x mod 2^(k - 1) ) - x
		final Sort intSort = mTheory.getNumericSort();

		final Term two = mTheory.rational(Rational.valueOf(BigInteger.valueOf(2), BigInteger.ONE), intSort);
		final Term twoPowWidth = mTheory
				.rational(Rational.valueOf(BigInteger.valueOf(2).pow(width - 1), BigInteger.ONE), intSort);

		if (lazyModulo) {
			final Term lazyPow = mTheory.rational(Rational.valueOf(BigInteger.valueOf(2).pow(width), BigInteger.ONE),
					intSort);
			final Term modulo = mTheory.term("mod", mTheory.term("mod", term, lazyPow), twoPowWidth);
			return mTheory.term("-", mTheory.term("*", two, modulo), mTheory.term("mod", term, lazyPow));
		} else {
			final Term modulo = mTheory.term("mod", term, twoPowWidth);
			return mTheory.term("-", mTheory.term("*", two, modulo), term);		}


	}

	// calculates power of two if exponent is a constant, otherwise this is not
	// implemented in the SMT integer theory
	private Term pow2(final Term term) {
		assert term.getSort().isNumericSort();
		if (term instanceof ConstantTerm) {
			final Sort intSort = mTheory.getNumericSort();
			final ConstantTerm constTerm = (ConstantTerm) term;
			final Term twoPow;
			if (constTerm.getValue() instanceof Rational) {
				final Rational ratint = (Rational) constTerm.getValue();
				twoPow = mTheory.rational(
						Rational.valueOf(BigInteger.valueOf(2).pow(ratint.numerator().intValue()), BigInteger.ONE),
						intSort);
			} else {
				final BigInteger bigint = (BigInteger) constTerm.getValue();
				twoPow = mTheory.rational(
						Rational.valueOf(BigInteger.valueOf(2).pow(bigint.intValue()), BigInteger.ONE), intSort);
			}
			return twoPow;
		}
		throw new UnsupportedOperationException("function pow2 not implemented");
		// return term;
	}

	private boolean isBitVecSort(final Sort sort) {
		if (sort.getName().equals("BitVec")) {
			return true;
		}
		return false;
	}

	private Sort translateSort(final Sort sort) {
		final Sort result;
		if (isBitVecSort(sort)) {
			result = mTheory.getNumericSort();
		} else {
			throw new UnsupportedOperationException("Unsupported sort: " + sort);
		}
		return result;
	}

	public LinkedHashMap<Term, Term> getVarMap() {
		return mVariableMap;
	}

	public LinkedHashMap<Term, Term> getReversedVarMap() {
		return mReversedVarMap;
	}

	private boolean overaproxWithVars(final ApplicationTerm appTerm) {
		final FunctionSymbol fsym = appTerm.getFunction();
		if (fsym.isIntern()) {
			switch (fsym.getName()) {
			case "bvand":
			case "bvor":
			case "bvxor":
			case "bvashr":
			case "bvshl":
			case "bvlshr": {
				return true;
			}
			default: {
				// not a bit-wise function symbol
				return false;
			}
			}
		}
		return false;
	}
	public Set<Term> getOverapproxVariables() {
		return mOverapproxVariables;
	}

	public boolean wasOverapproximation() {
		return mIsOverapproximation;
	}
}