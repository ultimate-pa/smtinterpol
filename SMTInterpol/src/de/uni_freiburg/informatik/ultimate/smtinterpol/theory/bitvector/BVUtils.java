package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.LogicSimplifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
/*
 * Copyright (C) 2020-2021 Max Barth (Max.Barth95@gmx.de)
 * Copyright (C) 2020-2021 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */

public class BVUtils {
	private final Theory mTheory;
	private final LogicSimplifier mUtils;

	public BVUtils(final Theory theory, final LogicSimplifier utils) {
		mTheory = theory;
		mUtils = utils;
	}

	/*
	 * setting the return value of this function to false, will deactivate all constant optimizations
	 */
	public boolean isConstRelation(final Term lhs, final Term rhs) {
		if ((lhs instanceof ConstantTerm)) {
			if (rhs == null) {
				return true;
			} else if (rhs instanceof ConstantTerm) {
				return true;
			}
		}
		return false;
	}

	/*
	 * returns the bit string of #b or #x Constant Terms.
	 * (_bvi j) Constants are replaced by #b constants beforehand
	 */
	public static String getConstAsString(final ConstantTerm ct) {
		if (ct.getSort().isBitVecSort()) {
			String bitString;
			assert (ct.getValue() instanceof String);
			bitString = (String) ct.getValue();
			if (bitString.startsWith("#b")) {
				bitString = (String) ct.getValue();
				return bitString.substring(2);
			} else if (bitString.startsWith("#x")) {
				// #xX of sort (_ BitVec m) where m is 4 times the number of digits in X.
				final String number = new BigInteger(bitString.substring(2), 16).toString(2);
				final int size = Integer.valueOf(ct.getSort().getIndices()[0]);
				final String repeated = new String(new char[size - number.length()]).replace("\0", "0");
				return repeated + number;
			}
		}
		throw new UnsupportedOperationException("Can't convert to bitstring: " + ct);
	}

	/*
	 * replaces (_bvi j) constants by #b constants
	 */
	public Term getBvConstAsBinaryConst(final FunctionSymbol fsym, final Sort sort) {
		if (sort.isBitVecSort()) {
			final String name = fsym.getName();
			assert name.matches("bv\\d+");
			String value = new BigInteger(name.substring(2)).toString(2);
			final int size = Integer.valueOf(sort.getIndices()[0]);
			if (value.length() > size) {
				final int overhead = value.length() - size;
				value = value.substring(overhead);
			} else {
				final String repeated = new String(new char[size - value.length()]).replace("\0", "0");
				value = repeated + value;
			}
			return mTheory.binary("#b" + value);
		}
		throw new UnsupportedOperationException("Can't convert bv constant: " + fsym.getName());
	}


	/*
	 * normalization of bitvec equalities,
	 * eliminates concatenations with perfect match:
	 * a :: b = c :: d replaced by a = c && c = d
	 * with a,c and b, d being of same size.
	 */
	public Term eliminateConcatPerfectMatch(final FunctionSymbol fsym, final Term lhs, final Term rhs) {
		assert fsym.getName().equals("=");
		final List<Term> matchresult = new ArrayList<>();

		if (!((lhs instanceof ApplicationTerm) && (rhs instanceof ApplicationTerm))) {
			return null;
		}
		final ApplicationTerm aplhs = (ApplicationTerm) lhs;
		final ApplicationTerm aprhs = (ApplicationTerm) rhs;
		if (!(aplhs.getFunction().getName().equals("concat") && aprhs.getFunction().getName().equals("concat"))) {
			return null;
		}
		if (aplhs.getParameters()[0].getSort().getIndices()
				.equals(aprhs.getParameters()[0].getSort().getIndices())) {
			final Term matchConj1 = mTheory.term("=", aplhs.getParameters()[0], aprhs.getParameters()[0]);
			final Term matchConj2 = mTheory.term("=", aplhs.getParameters()[1], aprhs.getParameters()[1]);
			matchresult.add(simplifyBinaryBitVecEquality(matchConj1));
			matchresult.add(simplifyBinaryBitVecEquality(matchConj2));
		} else {
			return null;
		}

		Term[] result = new Term[matchresult.size()];
		result = matchresult.toArray(result);
		return mTheory.and(result);
	}

	/*
	 * eliminates concatenations with NO match:
	 * That means, a,b and c have different size;
	 * a :: b = c is replaced by b = extract(0, b.length, c) AND a = extract( b.length , a.length, c)
	 * Can only be called on binary equalities.
	 */
	public Term eliminateConcatNoMatch(final FunctionSymbol fsym, final Term lhs, final Term rhs) {
		assert fsym.getName().equals("=");
		assert lhs.getSort().isBitVecSort();
		assert rhs.getSort().isBitVecSort();

		ApplicationTerm apTermConcat = null;
		Term concatResult = null;
		if (lhs instanceof ApplicationTerm) {
			if (((ApplicationTerm) lhs).getFunction().getName().equals("concat")) {
				apTermConcat = (ApplicationTerm) lhs;
				concatResult = rhs;
			}
		}
		if (rhs instanceof ApplicationTerm) {
			if (((ApplicationTerm) rhs).getFunction().getName().equals("concat")) {
				if (concatResult != null) {
					// concat on both sides
					// select propagation will take care of this
				} else {
					apTermConcat = (ApplicationTerm) rhs;
					concatResult = lhs;
				}

			}
		}
		if ((apTermConcat == null) || (concatResult == null)) {
			return null;
		}

		// selectIndices[0] >= selectIndices[1]
		final String[] selectIndices1 = new String[2];
		selectIndices1[0] =
				String.valueOf((Integer.parseInt(apTermConcat.getParameters()[1].getSort().getIndices()[0]) - 1));
		selectIndices1[1] = "0";
		// (_ extract i j)
		final FunctionSymbol extractLower =
				mTheory.getFunctionWithResult("extract", selectIndices1, null,
						concatResult.getSort());
		final Term extractLowerConcatResult = propagateExtract(extractLower, concatResult);
		final String[] selectIndices2 = new String[2];
		selectIndices2[0] =
				String.valueOf((Integer.parseInt(concatResult.getSort().getIndices()[0]) - 1));
		selectIndices2[1] =
				String.valueOf((Integer.parseInt(concatResult.getSort().getIndices()[0])
						- Integer.parseInt(apTermConcat.getParameters()[0].getSort().getIndices()[0])));
		final FunctionSymbol extractHigher =
				mTheory.getFunctionWithResult("extract", selectIndices2, null,
						concatResult.getSort());

		final Term extractHigherConcatResult = propagateExtract(extractHigher, concatResult);

		final Term matchConj1 = mTheory.term("=", apTermConcat.getParameters()[0], extractHigherConcatResult);
		final Term matchConj2 = mTheory.term("=", apTermConcat.getParameters()[1], extractLowerConcatResult);

		return mTheory.and(simplifyBinaryBitVecEquality(matchConj1),
				simplifyBinaryBitVecEquality(matchConj2));
	}

	/*
	 * bvadd, bvudiv, bvmul
	 */
	public Term simplifyArithmeticConst(final FunctionSymbol fsym, final Term lhs, final Term rhs) {
		final BigInteger lhsInt = new BigInteger(getConstAsString((ConstantTerm) lhs), 2);
		final BigInteger rhsInt = new BigInteger(getConstAsString((ConstantTerm) rhs), 2);
		String calc;
		final int size = Integer.valueOf(lhs.getSort().getIndices()[0]);
		if (fsym.getName().equals("bvadd")) {
			final BigInteger add = lhsInt.add(rhsInt);
			final BigInteger result = add.mod(BigInteger.valueOf(2).pow(size));
			calc = result.toString(2);
		} else if (fsym.getName().equals("bvudiv")) {
			// truncated integer division
			if (!rhsInt.equals(BigInteger.ZERO)) {
				final BigInteger divide = lhsInt.divide(rhsInt);
				final BigInteger result = divide.mod(BigInteger.valueOf(2).pow(size));
				calc = result.toString(2);
			} else {
				// value fixed to #b111...
				final String repeated = new String(new char[size]).replace("\0", "1");
				calc = repeated;
			}
		} else if (fsym.getName().equals("bvurem")) {
			if (!rhsInt.equals(BigInteger.ZERO)) {
				final BigInteger remainder = lhsInt.remainder(rhsInt);
				final BigInteger result = remainder.mod(BigInteger.valueOf(2).pow(size));
				calc = result.toString(2);
			} else {
				// value fixed to lhs
				calc = lhsInt.toString(2);
			}

		} else if (fsym.getName().equals("bvmul")) {
			// multiplication mod 2^m
			final BigInteger multiplication = lhsInt.multiply(rhsInt);
			final BigInteger result = multiplication.mod(BigInteger.valueOf(2).pow(size));
			calc = result.toString(2);
		} else if (fsym.getName().equals("bvsub")) {
			final BigInteger sub = lhsInt.subtract(rhsInt);
			final BigInteger result = sub.mod(BigInteger.valueOf(2).pow(size));
			calc = result.toString(2);
		} else {
			throw new UnsupportedOperationException("unknown function symbol: " + fsym.getName());
		}
		assert size >= calc.length();
		final String repeated = new String(new char[size - calc.length()]).replace("\0", "0");
		final String resultconst = "#b" + repeated + calc;
		return mTheory.binary(resultconst);
	}

	/*
	 * bvand, bvor
	 */
	public Term simplifyLogicalConst(final FunctionSymbol fsym, final Term lhs, final Term rhs) {
		String resultconst = "#b";
		final String constRHS = getConstAsString((ConstantTerm) lhs);
		final String constLHS = getConstAsString((ConstantTerm) rhs);
		for (int i = 0; i < constRHS.length(); i++) {
			final char first = constRHS.charAt(i);
			final char second = constLHS.charAt(i);
			// TODO if ((lhsAsString.charAt(i) == '1') && (rhsAsString.charAt(i) == '0')) {
			if (fsym.getName().equals("bvand")) {
				if ((Character.compare(first, second) == 0) && (Character.compare(first, '1') == 0)) {
					resultconst = resultconst + "1";
				} else {
					resultconst = resultconst + "0";
				}
			} else if (fsym.getName().equals("bvor")) {
				if ((Character.compare(first, second) == 0) && (Character.compare(first, '0') == 0)) {
					resultconst = resultconst + "0";
				} else {
					resultconst = resultconst + "1";
				}
			} else {
				throw new UnsupportedOperationException("unknown function symbol: " + fsym.getName());
			}
		}
		assert (constRHS.length() + 2) == resultconst.length();
		return mTheory.binary(resultconst);
	}

	public Term simplifyConcatConst(final FunctionSymbol fsym, final Term lhs, final Term rhs) {
		assert fsym.getName().equals("concat");
		final String result = "#b" + getConstAsString((ConstantTerm) lhs)
		.concat(getConstAsString((ConstantTerm) rhs));
		final Term concat = mTheory.binary(result);
		return concat;
	}

	/*
	 * bvshl, bvlshr
	 */
	public Term simplifyShiftConst(final FunctionSymbol fsym, final Term lhs, final Term rhs) {
		String resultconst = "#b";
		final String lhsString = getConstAsString((ConstantTerm) lhs);
		final BigInteger rhsBigInt = new BigInteger(getConstAsString((ConstantTerm) rhs), 2);
		final BigInteger lhslenth = new BigInteger(String.valueOf(lhsString.length()));

		if (fsym.getName().equals("bvshl")) {
			if (lhslenth.compareTo(rhsBigInt) <= 0) {
				final String repeated = new String(new char[lhslenth.intValue()]).replace("\0", "0");
				resultconst = resultconst + repeated;
			} else {
				final int rhsInt = rhsBigInt.intValue();
				final String repeated = new String(new char[rhsInt]).replace("\0", "0");
				resultconst = resultconst + lhsString.substring(rhsInt, lhslenth.intValue()) + repeated;

			}
		} else if (fsym.getName().equals("bvlshr")) {
			if (lhslenth.compareTo(rhsBigInt) <= 0) {
				final String repeated = new String(new char[lhslenth.intValue()]).replace("\0", "0");
				resultconst = resultconst + repeated;
			} else {
				final int rhsInt = rhsBigInt.intValue();
				final String repeated = new String(new char[rhsInt]).replace("\0", "0");
				resultconst = resultconst + repeated + lhsString.substring(0, lhslenth.intValue() - rhsInt);
			}

		} else {
			throw new UnsupportedOperationException("unknown function symbol: " + fsym.getName());
		}

		return mTheory.binary(resultconst);
	}


	public Term simplifyNegConst(final FunctionSymbol fsym, final Term term) {
		assert fsym.getName().equals("bvneg");
		final BigInteger bigint = new BigInteger(getConstAsString((ConstantTerm) term), 2);
		if (bigint.equals(BigInteger.ZERO)) {
			return term;
		}
		final String calc;
		final int size = Integer.valueOf(term.getSort().getIndices()[0]);

		final BigInteger result = BigInteger.valueOf(2).pow(size).subtract(bigint);
		calc = result.toString(2);
		assert size >= calc.length();
		final String repeated = new String(new char[size - calc.length()]).replace("\0", "0");
		final String resultconst = "#b" + repeated + calc;
		return mTheory.binary(resultconst);
	}

	public Term simplifyNotConst(final FunctionSymbol fsym, final Term term) {
		String resultconst = "#b";
		final String termAsString = getConstAsString((ConstantTerm) term);
		assert fsym.getName().equals("bvnot");
		for (int i = 0; i < termAsString.length(); i++) {
			if (termAsString.charAt(i) == '1') {
				resultconst = resultconst + "0";
			} else {
				resultconst = resultconst + "1";
			}
		}
		return mTheory.binary(resultconst);
	}



	public Term simplifySelectConst(final FunctionSymbol fsym, final Term term) {
		// (_ extract i j)
		// (_ BitVec l), 0 <= j <= i < l
		// (_ extract 7 5) 00100000 = 001
		// (_ extract 7 7) 10000000 = 1
		// Result length = i - j + 1
		String resultconst = "#b";
		assert fsym.getName().equals("extract");
		final String parameterAsString = getConstAsString((ConstantTerm) term);
		final int size = parameterAsString.length();
		final int idx1 = size - Integer.parseInt(fsym.getIndices()[1]);
		final int idx2 = size - Integer.parseInt(fsym.getIndices()[0]) - 1;
		resultconst = resultconst + parameterAsString.substring(idx2, idx1);
		return mTheory.binary(resultconst);
	}

	public Term simplifyBvultConst(final FunctionSymbol fsym, final Term lhs, final Term rhs) {
		if (fsym != null) {
			assert fsym.getName().equals("bvult");
		}
		final String lhsAsString = getConstAsString((ConstantTerm) lhs);
		final String rhsAsString = getConstAsString((ConstantTerm) rhs);
		for (int i = 0; i < lhsAsString.length(); i++) {
			if ((lhsAsString.charAt(i) == '1') && (rhsAsString.charAt(i) == '0')) {
				return mTheory.mFalse;
			} else if ((lhsAsString.charAt(i) == '0') && (rhsAsString.charAt(i) == '1')) {
				return mTheory.mTrue;
			}
		}
		return mTheory.mFalse; // both strings are equal
	}

	public Term simplifyBvslXConst(final FunctionSymbol fsym, final Term lhs, final Term rhs) {
		assert fsym.getName().equals("bvslt") || fsym.getName().equals("bvsle");
		final String lhsAsString = getConstAsString((ConstantTerm) lhs);
		final String rhsAsString = getConstAsString((ConstantTerm) rhs);
		// both strings are equal
		if (lhsAsString.equals(rhsAsString)) {
			if (fsym.getName().equals("bvslt")) {
				return mTheory.mFalse;
			} else {
				return mTheory.mTrue;
			}
		}
		// diffrent signes
		if ((lhsAsString.charAt(0) == '1') && (rhsAsString.charAt(0) == '0')) {
			return mTheory.mTrue;
		} else if ((lhsAsString.charAt(0) == '0') && (rhsAsString.charAt(0) == '1')) {
			return mTheory.mFalse;
		}
		// same sign
		for (int i = 1; i < lhsAsString.length(); i++) {
			if ((lhsAsString.charAt(i) == '1') && (rhsAsString.charAt(i) == '0')) {
				if ((lhsAsString.charAt(0) == '0') && (rhsAsString.charAt(0) == '0')) {
					return mTheory.mFalse;
				} else { // both sides negated
					return mTheory.mTrue;
				}
			} else if ((lhsAsString.charAt(i) == '0') && (rhsAsString.charAt(i) == '1')) {
				if ((lhsAsString.charAt(0) == '0') && (rhsAsString.charAt(0) == '0')) {
					return mTheory.mTrue;
				} else { // both sides negated
					return mTheory.mFalse;
				}
			}
		}
		return mTheory.term(fsym, lhs, rhs); // should never be the case
	}

	// TODO add proof for all const optimizations
	public Term getProof(final Term optimized, final Term convertedApp, final IProofTracker tracker,
			final Annotation proofconst) {
		final Term lhs = tracker.getProvedTerm(convertedApp);
		final Term rewrite =
				tracker.buildRewrite(lhs, optimized, proofconst);
		// return mTracker.transitivity(mConvertedApp, rewrite);
		return tracker.intern(convertedApp, rewrite); // wenn in einem literal
	}

	/*
	 * (bvult s t) to (bvult (bvsub s t) 0)
	 * unused
	 */
	private Term normalizeBvult(final ApplicationTerm bvult) {
		final Theory theory = bvult.getTheory();
		final int size = Integer.valueOf(bvult.getParameters()[0].getSort().getIndices()[0]);
		final String repeated = new String(new char[size]).replace("\0", "0");
		final String zeroconst = "#b" + repeated;
		return theory.term("bvult", theory.term("bvsub", bvult.getParameters()),
				theory.binary(zeroconst));
	}

	/*
	 * replaces every inequality by its bvult abbreviation.
	 * Applies a few simplifications on constant terms and simple equalities
	 * uses recursion in some cases
	 */
	public Term getBvultTerm(final Term convert) {
		final ApplicationTerm appterm;
		if (convert instanceof ApplicationTerm) {
			appterm = (ApplicationTerm) convert;
		} else if (convert instanceof AnnotatedTerm) {
			final AnnotatedTerm convAnno = (AnnotatedTerm) convert;
			appterm = (ApplicationTerm) convAnno.getSubterm();
		} else {
			throw new UnsupportedOperationException("Not an Inequality");
		}
		assert appterm.getParameters().length == 2;
		final int size = Integer.valueOf(appterm.getParameters()[0].getSort().getIndices()[0]);
		final FunctionSymbol fsym = appterm.getFunction();
		final Theory theory = convert.getTheory();
		// selectIndices[0] >= selectIndices[1]
		final String[] selectIndices = new String[2];
		final int signBitIndex = size - 1;
		selectIndices[0] = String.valueOf(signBitIndex);
		selectIndices[1] = String.valueOf(signBitIndex);
		// (_ extract i j)
		final FunctionSymbol extract =
				mTheory.getFunctionWithResult("extract", selectIndices, null,
						appterm.getParameters()[0].getSort());
		if (fsym.isIntern()) {
			switch (fsym.getName()) {
			case "bvult": {
				if (appterm.getParameters()[0].equals(appterm.getParameters()[1])) {
					return mTheory.mFalse;
				}
				if (isConstRelation(appterm.getParameters()[0], appterm.getParameters()[1])) {
					return simplifyBvultConst(appterm.getFunction(), appterm.getParameters()[0],
							appterm.getParameters()[1]);
				}
				return appterm;
			}
			case "bvslt": {
				if (appterm.getParameters()[0].equals(appterm.getParameters()[1])) {
					return mTheory.mFalse;
				}
				if (isConstRelation(appterm.getParameters()[0], appterm.getParameters()[1])) {
					return simplifyBvslXConst(appterm.getFunction(), appterm.getParameters()[0],
							appterm.getParameters()[1]);
				}
				final Term equiBvult = theory.or(theory.not(theory.or(
						theory.not(theory.term("=",
								theory.term(extract, appterm.getParameters()[0]),
								theory.binary("#b1"))),
						theory.not(theory.term("=",
								theory.term(extract, appterm.getParameters()[1]),
								theory.binary("#b0"))))),

						theory.not(theory.or(
								theory.not(theory.term("=",
										theory.term(extract, appterm.getParameters()[0]),
										theory.term(extract, appterm.getParameters()[1]))),
								theory.not(theory.term("bvult", appterm.getParameters()[0],
										appterm.getParameters()[1])))));
				return equiBvult;
			}
			case "bvule": {
				// (bvule s t) abbreviates (or (bvult s t) (= s t))
				final Term bvult =
						theory.term("bvult", appterm.getParameters()[0], appterm.getParameters()[1]);
				return theory.or(bvult, theory.term("=", appterm.getParameters()[0], appterm.getParameters()[1]));
			}
			case "bvsle": {
				if (isConstRelation(appterm.getParameters()[0], appterm.getParameters()[1])) {
					return simplifyBvslXConst(appterm.getFunction(), appterm.getParameters()[0],
							appterm.getParameters()[1]);
				}
				final Term bvult =
						theory.term("bvult", appterm.getParameters()[0], appterm.getParameters()[1]);
				final Term bvule = theory.or(bvult, theory.term("=", appterm.getParameters()[0], appterm.getParameters()[1]));
				final Term equiBvule = theory.or(
						theory.not(theory.or(
								theory.not(theory.term("=",
										theory.term(extract, appterm.getParameters()[0]),
										theory.binary("#b1"))),
								theory.not(theory.term("=",
										theory.term(extract, appterm.getParameters()[1]),
										theory.binary("#b0"))))),
						theory.not(theory.or(
								theory.not(theory.term("=",
										theory.term(extract, appterm.getParameters()[0]),
										theory.term(extract, appterm.getParameters()[1]))),
								theory.not(bvule
										))));

				return equiBvule;
			}
			case "bvugt": {
				if (appterm.getParameters()[0].equals(appterm.getParameters()[1])) {
					return mTheory.mFalse;
				}
				// (bvugt s t) abbreviates (bvult t s)
				if (isConstRelation(appterm.getParameters()[0], appterm.getParameters()[1])) {
					return simplifyBvultConst(null, appterm.getParameters()[1],
							appterm.getParameters()[0]);
				}
				return theory.term("bvult", appterm.getParameters()[1], appterm.getParameters()[0]);
			}
			case "bvsgt": {
				if (appterm.getParameters()[0].equals(appterm.getParameters()[1])) {
					return mTheory.mFalse;
				}
				// (bvsgt s t) abbreviates (bvslt t s)
				return getBvultTerm(theory.term("bvslt", appterm.getParameters()[1], appterm.getParameters()[0]));
			}
			case "bvuge": {
				// (bvuge s t) abbreviates (or (bvult t s) (= s t))
				final Term bvult;
				if (isConstRelation(appterm.getParameters()[0], appterm.getParameters()[1])) {
					bvult = simplifyBvultConst(null, appterm.getParameters()[1],
							appterm.getParameters()[0]);
				} else {
					bvult = theory.term("bvult", appterm.getParameters()[1], appterm.getParameters()[0]);
				}
				return theory.or(bvult, theory.term("=", appterm.getParameters()[0], appterm.getParameters()[1]));
			}
			case "bvsge": {
				// (bvsge s t) abbreviates (bvsle t s)
				return getBvultTerm(theory.term("bvsle", appterm.getParameters()[1], appterm.getParameters()[0]));
			}
			default: {
				throw new UnsupportedOperationException("Not an Inequality function symbol: " + fsym.getName());
			}
			}
		}
		throw new UnsupportedOperationException("Not an Inequality");
	}


	/*
	 * Bit Mask Elimination simplifies bvand, bvor functions where one hand side is a constant.
	 * We determine the result of the function as much as possible by the given constant (absorbingElement).
	 * everything else (neutralElement in the constant) is selected from the non-constant argument.
	 */
	public Term bitMaskElimination(final Term term) {
		Term bitMask = null;
		final String[] indices = new String[2];

		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) term;
			final char absorbingElement;
			final char neutralElement;
			if (appterm.getFunction().getName().equals("bvand")) {
				absorbingElement = '0';
				neutralElement = '1';
			} else if (appterm.getFunction().getName().equals("bvor")) {
				absorbingElement = '1';
				neutralElement = '0';
			} else {
				return term;
			}
			final Term lhs = appterm.getParameters()[0];
			final Term rhs = appterm.getParameters()[1];
			final String constAsString;
			Term varTerm;
			if ((lhs instanceof ConstantTerm) && ((rhs instanceof TermVariable) || (rhs instanceof ApplicationTerm))) {
				constAsString = getConstAsString((ConstantTerm) lhs);
				varTerm = rhs;
			} else if ((rhs instanceof ConstantTerm)
					&& ((lhs instanceof TermVariable) || (lhs instanceof ApplicationTerm))) {
				constAsString = getConstAsString((ConstantTerm) rhs);
				varTerm = lhs;
			} else {
				return term;
			}

			String constSubString = "#b";
			indices[0] = String.valueOf(constAsString.length() - 1);

			for (int i = 0; i < constAsString.length(); i++) { // iterates from left to right over the BitVec
				final char ch = constAsString.charAt(i);
				if (ch == absorbingElement) {
					constSubString = constSubString + ch;
					if (i > 0) {
						if (constAsString.charAt(i - 1) == neutralElement) {
							// indices.clone() is important, otherwise the term changes by altering the array!
							final FunctionSymbol extract =
									mTheory.getFunctionWithResult("extract", indices.clone(), null,
											appterm.getParameters()[0].getSort());
							final Term select = mTheory.term(extract, varTerm);

							if (bitMask != null) {
								bitMask = mTheory.term("concat", bitMask, select);
							} else {
								bitMask = select;
							}
						}
					}
					indices[0] = String.valueOf(constAsString.length() - i - 2);
					if (i == constAsString.length() - 1) {
						if (bitMask != null) {
							bitMask = mTheory.term("concat", bitMask, mTheory.binary(constSubString));
						} else {
							bitMask = mTheory.binary(constSubString);
						}
					}
				} else {
					if (!constSubString.equals("#b")) {
						if (bitMask != null) {
							bitMask = mTheory.term("concat", bitMask, mTheory.binary(constSubString));
						} else {
							bitMask = mTheory.binary(constSubString);
						}
					}
					constSubString = "#b";
					indices[1] = String.valueOf(constAsString.length() - i - 1);
					// Case end of Vector
					if (i == constAsString.length() - 1) {
						final FunctionSymbol extract =
								mTheory.getFunctionWithResult("extract", indices.clone(), null,
										appterm.getParameters()[0].getSort());
						final Term select = mTheory.term(extract, varTerm);
						if (bitMask != null) {
							bitMask = mTheory.term("concat", bitMask, select);
						} else {
							bitMask = select;
						}
					}
				}

			}
			return bitMask;
		}
		return term;
	}

	/*
	 * propagates a select over concat and bitwise functions to its arguments
	 * smallers the bitvec size of the function (less work for bitblasting)
	 */
	public Term propagateExtract(final FunctionSymbol fsym, final Term param) {
		assert fsym.getName().equals("extract");
		final int lowerIndex = Integer.parseInt(fsym.getIndices()[1]);
		final int upperIndex = Integer.parseInt(fsym.getIndices()[0]);
		assert lowerIndex <= upperIndex;
		if (param instanceof ApplicationTerm) {
			final ApplicationTerm subTerm = (ApplicationTerm) param;
			final FunctionSymbol subFsym = subTerm.getFunction();
			if (subFsym.isIntern()) {
				switch (subFsym.getName()) {
				case "concat": {
					// length beider argumente,
					final int rhsSize = Integer.parseInt(subTerm.getParameters()[1].getSort().getIndices()[0]);
					if (upperIndex > rhsSize - 1) {
						if (lowerIndex > rhsSize - 1) {
							// selecting from lhs of concat

							final String[] selectIndices = new String[2];
							selectIndices[0] =
									String.valueOf(upperIndex - rhsSize);
							selectIndices[1] =
									String.valueOf(lowerIndex - rhsSize);

							final FunctionSymbol extract =
									mTheory.getFunctionWithResult("extract", selectIndices, null,
											subTerm.getParameters()[0].getSort());
							if (isConstRelation(subTerm.getParameters()[0], null)) {
								return simplifySelectConst(extract, subTerm.getParameters()[0]);
							}
							return mTheory.term(extract, subTerm.getParameters()[0]);
						} else {
							// selecting from both sides of concat

							// select from lhs of concat
							final String[] selectIndices1 = new String[2];
							selectIndices1[0] = String.valueOf(upperIndex - rhsSize);
							selectIndices1[1] = "0";
							final FunctionSymbol extractLhs =
									mTheory.getFunctionWithResult("extract", selectIndices1, null,
											subTerm.getParameters()[0].getSort());

							// select from rhs of concat
							final String[] selectIndices2 = new String[2];
							selectIndices2[0] = String.valueOf(rhsSize - 1); // rhs size
							selectIndices2[1] = String.valueOf(lowerIndex);

							final FunctionSymbol extractRhs =
									mTheory.getFunctionWithResult("extract", selectIndices2, null,
											subTerm.getParameters()[1].getSort());
							Term selectLhs = mTheory.term(extractLhs, subTerm.getParameters()[0]);
							Term selectRhs = mTheory.term(extractRhs, subTerm.getParameters()[1]);
							if (isConstRelation(subTerm.getParameters()[0], null)) {
								selectLhs = simplifySelectConst(extractLhs, subTerm.getParameters()[0]);
							}
							if (isConstRelation(subTerm.getParameters()[1], null)) {
								selectRhs = simplifySelectConst(extractRhs, subTerm.getParameters()[1]);
							}
							return mTheory.term("concat", selectLhs, selectRhs);

						}

					} else {
						// selecting from rhs of concat
						final FunctionSymbol extract =
								mTheory.getFunctionWithResult("extract", fsym.getIndices(), null,
										subTerm.getParameters()[1].getSort());
						if (isConstRelation(subTerm.getParameters()[1], null)) {
							return simplifySelectConst(extract, subTerm.getParameters()[1]);
						}
						return mTheory.term(extract, subTerm.getParameters()[1]);
					}

				}
				case "extract": {
					// term[x : y][i : j] replaced by term[y + i + (i - j) : y + j]
					final int innerExtractLowerIndex = Integer.parseInt(subFsym.getIndices()[1]);
					final int difference = upperIndex - lowerIndex;
					final String[] selectIndices = new String[2];
					selectIndices[0] = String.valueOf(lowerIndex + innerExtractLowerIndex + difference);
					selectIndices[1] = String.valueOf(lowerIndex + innerExtractLowerIndex);
					final FunctionSymbol extract =
							mTheory.getFunctionWithResult("extract", selectIndices, null,
									subTerm.getParameters()[0].getSort());
					if (isConstRelation(subTerm.getParameters()[0], null)) {
						return simplifySelectConst(extract, subTerm.getParameters()[0]);
					}
					return mTheory.term(extract, subTerm.getParameters()[0]);

				}
				case "bvand": {
					assert subTerm.getParameters().length == 2;
					return mTheory.term("bvand", mTheory.term(fsym, subTerm.getParameters()[0]),
							mTheory.term(fsym, subTerm.getParameters()[1]));
				}
				case "bvor": {
					assert subTerm.getParameters().length == 2;
					return mTheory.term("bvor", mTheory.term(fsym, subTerm.getParameters()[0]),
							mTheory.term(fsym, subTerm.getParameters()[1]));
				}
				case "bvnot": {
					assert subTerm.getParameters().length == 1;
					return mTheory.term("bvnot", mTheory.term(fsym, subTerm.getParameters()[0]));

				}
				default: {
					if (isConstRelation(param, null)) {
						return simplifySelectConst(fsym, param);
					}
					return mTheory.term(fsym, param);
				}
				}

			}
		}
		if (isConstRelation(param, null)) {
			return simplifySelectConst(fsym, param);
		}
		return mTheory.term(fsym, param);

	}

	/*
	 * iterates over a formula of form (not (or (not (= b a)) (not (= a c))))
	 * often provided by mUtils.convertEq (called in TermCompiler)
	 */
	public Term iterateOverBvEqualites(final Term convertedEquality) {
		// System.out.println(convertedEquality.toStringDirect());
		if (convertedEquality.equals(mTheory.mTrue) || convertedEquality.equals(mTheory.mFalse)) {
			return convertedEquality;
		}
		assert convertedEquality instanceof ApplicationTerm;
		final ApplicationTerm equalities = (ApplicationTerm) convertedEquality;

		if (equalities.getFunction().getName().equals("not")) {
			// called if the input formula is of form (= a b c ...)
			final ApplicationTerm disjunction = (ApplicationTerm) equalities.getParameters()[0];
			final Term[] orderedDisjTerms = new Term[disjunction.getParameters().length];
			for (int i = 0; i < disjunction.getParameters().length; i++) {
				final Term para = disjunction.getParameters()[i];
				assert para instanceof ApplicationTerm;
				final ApplicationTerm apPara = (ApplicationTerm) para;
				assert apPara.getFunction().getName().equals("not");

				orderedDisjTerms[i] = simplifyBinaryBitVecEquality(apPara.getParameters()[0]);
			}
			final Term result = mTheory.not(mTheory.or(orderedDisjTerms));
			// System.out.println(result.toStringDirect());
			return result;
		} else if (equalities.getFunction().getName().equals("=")) {
			assert equalities.getParameters().length == 2; // if false, call mUtils.convertEq first
			final Term simpAndOrder = simplifyBinaryBitVecEquality(equalities);
			return simpAndOrder;
		} else {
			throw new UnsupportedOperationException("Not an Equality");
		}

	}

	/**
	 * Input is a binary equality.
	 *
	 * Simplifies trivial equalities.
	 * calls orderParameters, eliminateConcatPerfectMatch and eliminateConcatNoMatch
	 *
	 * Retruns true, false, an equality or a mUtils.convertAnd() of two equalities
	 **/
	private Term simplifyBinaryBitVecEquality(final Term equality) {
		ApplicationTerm appterm;
		if (equality instanceof ApplicationTerm) {
			appterm = (ApplicationTerm) equality;
		} else if (equality instanceof AnnotatedTerm) {
			final AnnotatedTerm convAnno = (AnnotatedTerm) equality;
			appterm = (ApplicationTerm) convAnno.getSubterm();
		} else {
			throw new UnsupportedOperationException("Not an Equality");
		}
		if (equality.equals(mTheory.mTrue) || equality.equals(mTheory.mFalse)) {
			return equality;
		}
		assert appterm.getFunction().getName().equals("=");
		appterm = (ApplicationTerm) orderParameters(appterm.getFunction(), appterm.getParameters());
		final Term lhs = appterm.getParameters()[0];
		final Term rhs = appterm.getParameters()[1];

		if (lhs.equals(rhs)) {
			return mTheory.mTrue;
		}
		if (isConstRelation(lhs, rhs)) {
			if (getConstAsString((ConstantTerm) lhs).equals(getConstAsString((ConstantTerm) rhs))) {
				return mTheory.mTrue;
			} else
				return mTheory.mFalse;
		}
		final Term perfectMatch = eliminateConcatPerfectMatch(appterm.getFunction(), lhs, rhs);
		if (perfectMatch != null) {
			if (((ApplicationTerm) perfectMatch).getFunction().getName().equals("and")) {
				// Needs to be converted for iterateOverBvEqualities
				return mUtils.convertAnd(perfectMatch);
			} else {
				return perfectMatch;
			}
		}
		final Term noMatch = eliminateConcatNoMatch(appterm.getFunction(), lhs, rhs);
		if (noMatch != null) {
			if (((ApplicationTerm) noMatch).getFunction().getName().equals("and")) {
				return mUtils.convertAnd(noMatch);
			} else {
				return noMatch;
			}
		}
		return equality;
	}

	/*
	 * orders the parameter of input Term, if its a symmetric operand.
	 * Optimization for two cases:
	 * Case1:
	 * bvadd(a,b) = bvadd(b,a) ordered to bvadd(a,b) = bvadd(a,b) and can later be replaced by true
	 * Case2:
	 * In a more complex Term, bitblasting for bvadd(a,b) is only applied once.
	 * Otherwise we would bitblast twice, for bvadd(a,b) and bvadd(b,a).
	 * =, bvadd, bvmul, bvor, bvand
	 */
	public Term orderParameters(final FunctionSymbol fsym, final Term[] params) {
		assert params[0].getSort().isBitVecSort();
		assert params.length == 2;
		assert fsym.getName().equals("=")
		|| fsym.getName().equals("bvadd")
		|| fsym.getName().equals("bvmul")
		|| fsym.getName().equals("bvand")
		|| fsym.getName().equals("bvor"); // has to be a symetricFunction
		if (params[0].hashCode() < params[1].hashCode()) {
			return mTheory.term(fsym, params);
		} else if (params[0].hashCode() > params[1].hashCode()) {
			return mTheory.term(fsym, params[1],
					params[0]);
		} else {
			return mTheory.term(fsym, params);
		}
	}
}
