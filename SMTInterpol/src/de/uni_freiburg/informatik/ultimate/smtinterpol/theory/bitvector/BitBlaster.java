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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.BooleanVarAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom.TrueAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedArrayList;

public class BitBlaster {
	private final Clausifier mClausifier;
	private final Theory mTheory;
	private ScopedArrayList<Literal> mInputLiterals;
	public HashMap<Term, DPLLAtom> mBoolAtoms; // Maps Bool variable to Bool Atoms, contains (aux variables, bbAtoms..)
	private final ScopedArrayList<Clause> mClauses; // Output clauses
	private final HashMap<Term, Term[]> mEncTerms; // Term[0] is the least bit, the most right bit of the key(Term)
	private final HashMap<Term, Literal> mLiterals; // Maps encoded Atoms as Term to mInputLiterals
	public LinkedHashMap<Literal, Literal> mInputAtomMap; // Maps Input Literals to encoded atoms
	private Term mTrueConstBoolAtom;
	private Term mFalseConstBoolAtom;
	private int mStackLevel;



	public BitBlaster(final Clausifier clausifier, final Theory theory) {
		mClausifier = clausifier; // used for Timeout
		mTheory = theory;
		mInputAtomMap = new LinkedHashMap<>();
		mEncTerms = new HashMap<>();
		mBoolAtoms = new HashMap<>();
		mLiterals = new HashMap<>();
		mClauses = new ScopedArrayList<>();
	}


	/**
	 * Starts Bitblasting.
	 * allLiterals contains all set bitvector Literals and allTerms all terms from these literals.
	 * allTerms needs to contain all terms, subterms, constants, variables... but no relations(=, bvult...).
	 * allTerms is filled by BitVectorTheory.collectAllTerms().
	 * Use getClauses() to get the BB result Clauses and getBoolAtoms() to get the necessary Atoms.
	 **/
	public void bitBlasting(final ScopedArrayList<Literal> allLiterals,
			final LinkedHashSet<Term> allTerms, final int engineStackLevel) {
		mStackLevel = engineStackLevel;
		mInputLiterals = allLiterals;


		for (int i = 0; i < mInputLiterals.size(); i++) {
			final String atomPrefix = "At_" + i;
			final Term boolVar = createBoolAtom(atomPrefix);
			mLiterals.put(boolVar, mInputLiterals.get(i).getAtom());
			mInputAtomMap.put(mInputLiterals.get(i).getAtom(), mBoolAtoms.get(boolVar));
		}

		for (final Term term : allTerms) {
			// e(t), t in terms. Terms Size long Array of bool vars with e(t)_i being var at position i
			if (term.getSort().isBitVecSort() && !mEncTerms.containsKey(term)) {
				final ArrayDeque<Term> encode = new ArrayDeque<>();
				final ArrayDeque<Term> optimizeBVselections = new ArrayDeque<>();
				encode.push(term);
				while (!encode.isEmpty()) {
					final Term peek = encode.pop();
					if (!mEncTerms.containsKey(peek)) {
						if (peek instanceof ApplicationTerm) {
							final ApplicationTerm apPeek = (ApplicationTerm) peek;
							if (apPeek.getFunction().getName().equals("concat")) {
								encode.push(apPeek.getParameters()[0]);
								encode.push(apPeek.getParameters()[1]);
								optimizeBVselections.push(peek);
								continue;
							} else if ((apPeek.getFunction().getName().equals("extract")) ||
									(apPeek.getFunction().getName().equals("rotate_left")) ||
									(apPeek.getFunction().getName().equals("rotate_right")) ||
									(apPeek.getFunction().getName().equals("zero_extend")) ||
									(apPeek.getFunction().getName().equals("sign_extend")) ||
									(apPeek.getFunction().getName().equals("repeat"))) {
								encode.push(apPeek.getParameters()[0]);
								// optimization
								optimizeBVselections.push(peek);
								continue;
							}
						}
						getEncodedTerm(peek);
					}
				}
				// Encode concat, extract, etc after encoding their arguments.
				while (!optimizeBVselections.isEmpty()) {
					// Encode the most inner concat, extract... first (arguments have to be encoded before)
					getEncodedTerm(optimizeBVselections.pop());
				}

			}
		}
		// Propositional Skeleton is created in the Theory Solver.

		// add BVConstraint of Atoms as conjunct
		for (final Literal atom : mInputAtomMap.keySet()) {
			getBvConstraintAtom(getTerm(atom.getAtom()), mInputAtomMap.get(atom).getAtom().getSMTFormula(mTheory));
		}
		// add BVConstraint of all subterms as conjunct
		for (final Term term : allTerms) {
			if (mClausifier.getEngine().isTerminationRequested()) {
				return;
			}
			getBvConstraintTerm(term);
		}
	}

	/*
	 * for bvult literals, Literal.getSMTFormula(Theory) won't work, since this would return "(bvult #b0111 p4) == true"
	 */
	private Term getTerm(final Literal lit) {
		Term atom = lit.getAtom().getSMTFormula(mTheory);
		final ApplicationTerm apAtom = (ApplicationTerm) atom;
		if (apAtom.getParameters()[0] instanceof ApplicationTerm) {
			if (((ApplicationTerm) apAtom.getParameters()[0]).getFunction().getName().equals("bvult")) {
				atom = apAtom.getParameters()[0];
			}
		} else if (apAtom.getParameters()[1] instanceof ApplicationTerm) {
			if (((ApplicationTerm) apAtom.getParameters()[1]).getFunction().getName().equals("bvult")) {
				atom = apAtom.getParameters()[1];
			}
		}
		return atom;
	}

	/*
	 * Encodes bitvector Term in an Array of same length as the size of the bitvector Term.
	 * The Array contains Fresh Boolean Variables with name:
	 * "e(term)_i" where e stands for encoded, term is the input term (Its HashCode) and i the current position in the
	 * Array/BitVec
	 */
	private Term[] getEncodedTerm(final Term term) {
		assert term.getSort().isBitVecSort();
		if (mEncTerms.containsKey(term)) {
			return mEncTerms.get(term);
		}
		final BigInteger sizeBig = mTheory.toNumeral(term.getSort().getIndices()[0]);
		final int size = sizeBig.intValue();
		final Term[] boolvector = new Term[size];

		// optimization, select,concat, etc. is not encoded, instead we return the encoded argument
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm apTerm = (ApplicationTerm) term;
			if (apTerm.getFunction().isIntern()) {
				switch (apTerm.getFunction().getName()) {
				case "extract": {
					final Term[] encArgument = mEncTerms.get(apTerm.getParameters()[0]);
					final Term[] extractResult = Arrays.copyOfRange(encArgument,
							Integer.parseInt(apTerm.getFunction().getIndices()[1]),
							Integer.parseInt(apTerm.getFunction().getIndices()[0]) + 1);
					for (int i = 0; i < size; i++) {
						boolvector[i] = extractResult[i];
					}
					mEncTerms.put(term, boolvector);
					return boolvector;
				}
				case "concat": {
					final Term[] encArgument1 = mEncTerms.get(apTerm.getParameters()[0]);
					final Term[] encArgument2 = mEncTerms.get(apTerm.getParameters()[1]);
					for (int i = 0; i < encArgument2.length; i++) {
						boolvector[i] = encArgument2[i];
					}
					for (int i = 0; i < encArgument1.length; i++) {
						boolvector[encArgument2.length + i] = encArgument1[i];
					}
					mEncTerms.put(term, boolvector);
					return boolvector;
				}
				case "rotate_left": {
					final Term[] encArgument = mEncTerms.get(apTerm.getParameters()[0]);
					int rotationDistance = Integer.valueOf(apTerm.getFunction().getIndices()[0]);
					if (rotationDistance > encArgument.length) {
						rotationDistance = (rotationDistance % encArgument.length);
					}
					for (int i = 0; i < encArgument.length; i++) {
						if (i + rotationDistance < encArgument.length) {
							boolvector[i + rotationDistance] = encArgument[i];
						} else {
							boolvector[(i + rotationDistance) - encArgument.length] = encArgument[i];
						}

					}
					mEncTerms.put(term, boolvector);
					return boolvector;
				}
				case "rotate_right": {
					final Term[] encArgument = mEncTerms.get(apTerm.getParameters()[0]);
					int rotationDistance = Integer.valueOf(apTerm.getFunction().getIndices()[0]);
					if (rotationDistance > encArgument.length) {
						rotationDistance = (rotationDistance % encArgument.length);
					}
					for (int i = 0; i < encArgument.length; i++) {
						if (i - rotationDistance >= 0) {
							boolvector[i - rotationDistance] = encArgument[i];
						} else {
							boolvector[(i - rotationDistance) + (encArgument.length)] = encArgument[i];
						}

					}
					mEncTerms.put(term, boolvector);
					return boolvector;
				}
				case "zero_extend": {
					if ((mTrueConstBoolAtom == null) && (mFalseConstBoolAtom == null)) {
						mTrueConstBoolAtom = createBoolAtom("trueConst");
						mFalseConstBoolAtom = createBoolAtom("falseConst");
						final Literal[] trueLit = { mBoolAtoms.get(mTrueConstBoolAtom) };
						addClause(trueLit);
						final Literal[] falseLit = { mBoolAtoms.get(mFalseConstBoolAtom).negate() };
						addClause(falseLit);
					}
					final Term[] encArgument = mEncTerms.get(apTerm.getParameters()[0]);
					final int extendDistance = Integer.valueOf(apTerm.getFunction().getIndices()[0]);
					for (int i = 0; i < encArgument.length; i++) {
						boolvector[i] = encArgument[i];
					}
					for (int i = 0; i < extendDistance; i++) {
						boolvector[encArgument.length + i] = mFalseConstBoolAtom;
					}
					mEncTerms.put(term, boolvector);
					return boolvector;
				}
				case "sign_extend": {
					final Term[] encArgument = mEncTerms.get(apTerm.getParameters()[0]);
					final int extendDistance = Integer.valueOf(apTerm.getFunction().getIndices()[0]);
					for (int i = 0; i < encArgument.length; i++) {
						boolvector[i] = encArgument[i];
					}
					for (int i = 0; i < extendDistance; i++) {
						boolvector[encArgument.length + i] = encArgument[encArgument.length - 1];
					}
					mEncTerms.put(term, boolvector);
					return boolvector;
				}
				case "repeat": {
					final Term[] encArgument = mEncTerms.get(apTerm.getParameters()[0]);
					final int repetitions = Integer.valueOf(apTerm.getFunction().getIndices()[0]);
					for (int r = 0; r < repetitions; r++) {
						for (int i = 0; i < encArgument.length; i++) {
							boolvector[i + (encArgument.length * r)] = encArgument[i];
						}
					}
					mEncTerms.put(term, boolvector);
					return boolvector;
				}
				}
			}
		}
		if (term instanceof ConstantTerm) {
			// Optimization create only one literal for "true" and one for "false"
			if ((mTrueConstBoolAtom == null) && (mFalseConstBoolAtom == null)) {
				mTrueConstBoolAtom = createBoolAtom("trueConst");
				mFalseConstBoolAtom = createBoolAtom("falseConst");
				final Literal[] trueLit = { mBoolAtoms.get(mTrueConstBoolAtom) };
				addClause(trueLit);
				final Literal[] falseLit = { mBoolAtoms.get(mFalseConstBoolAtom).negate() };
				addClause(falseLit);
			}
			for (int i = 0; i < size; i++) {
				final String termstring = BVUtils.getConstAsString((ConstantTerm) term);
				if (termstring.charAt(termstring.length() - 1 - i) == '1') {
					boolvector[i] = mTrueConstBoolAtom;
				} else {
					boolvector[i] = mFalseConstBoolAtom;
				}
			}
			mEncTerms.put(term, boolvector);
			return boolvector;
		}

		for (int i = 0; i < size; i++) {
			final String termPrefix = "e_(" + term.hashCode() + ")_" + i; // must not contain | as symbol
			final Term boolVar = createBoolAtom(termPrefix);
			boolvector[i] = boolVar;
		}
		mEncTerms.put(term, boolvector);
		return boolvector;
	}

	/*
	 * Creates BVConstraint for Atom's
	 * For equals:
	 * (AND lhs_i = rhs_i) <=> encAtom
	 * For bvult:
	 * not(bvadd (lhs not(rhs)).cout) <=> encAtom
	 */
	private void getBvConstraintAtom(final Term atom, final Term encAtom) {
		if (atom instanceof ApplicationTerm) {
			final ApplicationTerm apAtom = (ApplicationTerm) atom;
			final Term lhs = apAtom.getParameters()[0];
			final Term rhs = apAtom.getParameters()[1];

			if (((ApplicationTerm) atom).getFunction().getName().equals("=")) {
				// (AND lhs_i = rhs_i) <=> encAtom
				final BigInteger sizeBig = mTheory.toNumeral(lhs.getSort().getIndices()[0]);
				final int size = sizeBig.intValue();
				final Term[] eqconj = new Term[size];
				final Literal atLit = getLiteral(encAtom);
				if (size == 1) { // after which size is bvcomp faster?
					for (int i = 0; i < size; i++) {
						// creates 2*size + 2^size Clauses, Only faster for small sizes
						final Literal lhsLit = getLiteral(mEncTerms.get(lhs)[i]);
						final Literal rhsLit = getLiteral(mEncTerms.get(rhs)[i]);
						final Literal[] lit1 = { atLit.negate(), lhsLit, rhsLit.negate() };
						addClause(lit1);
						final Literal[] lit2 = { atLit.negate(), lhsLit.negate(), rhsLit };
						addClause(lit2);
						eqconj[i] =
								mTheory.or(mTheory.and(mEncTerms.get(lhs)[i],
										mEncTerms.get(rhs)[i]),
										mTheory.and(mTheory.not(mEncTerms.get(rhs)[i]),
												mTheory.not(mEncTerms.get(lhs)[i])));
					}
					final Term eqconjunction = mTheory.and(eqconj);
					toClauses(mTheory.or(mTheory.not(eqconjunction), encAtom));
				} else {
					// Using bvcomp method to determine equality
					final Literal[] bvxnor = new Literal[size + 1];
					for (int i = 0; i < size; i++) {
						final Term boolVar = createBoolAtom(null);
						final Literal at = getLiteral(boolVar);
						final Literal lhsLit = getLiteral(mEncTerms.get(lhs)[i]);
						final Literal rhsLit = getLiteral(mEncTerms.get(rhs)[i]);

						final Literal[] lit1 = { at, lhsLit, rhsLit };
						addClause(lit1);
						final Literal[] lit2 = { at, lhsLit.negate(), rhsLit.negate() };
						addClause(lit2);
						final Literal[] lit3 = { at.negate(), lhsLit, rhsLit.negate() };
						addClause(lit3);
						final Literal[] lit4 = { at.negate(), lhsLit.negate(), rhsLit };
						addClause(lit4);
						bvxnor[i] = at.negate();
						final Literal[] lit5 = { atLit.negate(), at };
						addClause(lit5);
					}
					bvxnor[size] = atLit;
					addClause(bvxnor);
				}


			} else if (((ApplicationTerm) atom).getFunction().getName().equals("bvult")) {
				// bvult, holds if cout is false
				final Term bvult =
						mTheory.not(adder(mEncTerms.get(((ApplicationTerm) atom).getParameters()[0]),
								negate(mEncTerms.get(((ApplicationTerm) atom).getParameters()[1])),
								mTheory.mTrue, null).getSecond());

				final Literal bvultLit = getLiteral(bvult);
				final Literal atLit = getLiteral(encAtom);
				final Literal[] lit1 = { atLit.negate(), bvultLit };
				addClause(lit1);
				final Literal[] lit2 = { atLit, bvultLit.negate() };
				addClause(lit2);
			} else {
				throw new UnsupportedOperationException("Unknown Atom");
			}
		}
	}

	/*
	 * Bitblasting for all terms, reports the result as Clause to mClauses.
	 * If there exist an BitBlastngResult for this term, we'll add this instead
	 */
	private void getBvConstraintTerm(final Term term) {
		if (term instanceof TermVariable) {
			return;
		} else if (term instanceof ConstantTerm) {
			// getEncodedTerm deals with constants
			return;
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) term;
			final FunctionSymbol fsym = appterm.getFunction();
			// mClausifier.getLogger().info("Term Constraint: " + fsym.getName());
			if (appterm.getParameters().length == 0) {
				// uninterpreted constants
				return;
			}
			if (fsym.isIntern()) {
				switch (fsym.getName()) {
				case "=":
				case "and":
				case "or":
				case "not":
				case "ite": {
					// CClosure should have dealt with this.
					return;
				}
				}
				final Term[] encTerm = mEncTerms.get(term);
				Term[] conjunction = new Term[encTerm.length];
				switch (fsym.getName()) {
				case "bvand": {
					for (int i = 0; i < encTerm.length; i++) {
						final Term and = mTheory.and(mEncTerms.get(appterm.getParameters()[0])[i],
								mEncTerms.get(appterm.getParameters()[1])[i]);
						conjunction[i] = and;
					}
					break;
				}
				case "bvor": {
					for (int i = 0; i < encTerm.length; i++) {
						final Term or = mTheory.or(mEncTerms.get(appterm.getParameters()[0])[i],
								mEncTerms.get(appterm.getParameters()[1])[i]);
						conjunction[i] = or;
					}
					break;
				}
				case "bvnot": {
					for (int i = 0; i < encTerm.length; i++) {
						final Term not = mTheory.not(mEncTerms.get(appterm.getParameters()[0])[i]);
						conjunction[i] = not;
					}
					break;
				}
				// case "bvneg": {
				// break;
				// }
				case "bvadd": {
					adder(mEncTerms.get(appterm.getParameters()[0]), mEncTerms.get(appterm.getParameters()[1]),
							mTheory.mFalse, encTerm).getFirst();
					// return, clauses will be created and saved in the Adder
					return;
				}
				case "bvsub": {
					adder(mEncTerms.get(appterm.getParameters()[0]),
							negate(mEncTerms.get(appterm.getParameters()[1])),
							mTheory.mTrue, encTerm).getFirst();
					return;
				}
				case "bvmul": {
					final int stage =
							mTheory.toNumeral(appterm.getParameters()[1].getSort().getIndices()[0]).intValue() - 1;
					multiplier(appterm.getParameters()[0], appterm.getParameters()[1], stage, encTerm);
					return;
				}
				case "bvshl": {
					final int stage =
							mTheory.toNumeral(appterm.getParameters()[1].getSort().getIndices()[0]).intValue() - 1;
					conjunction = shift(appterm.getParameters()[0], appterm.getParameters()[1], stage, true);
					break;
				}
				case "bvlshr": {
					final int stage =
							mTheory.toNumeral(appterm.getParameters()[1].getSort().getIndices()[0]).intValue() - 1;
					conjunction = shift(appterm.getParameters()[0], appterm.getParameters()[1], stage, false);
					break;
				}
				case "concat": {
					// conjunction = concatArrays(mEncTerms.get(appterm.getParameters()[0]),
					// mEncTerms.get(appterm.getParameters()[1]));
					// break;
					return;
				}
				case "extract":
				case "zero_extend":
				case "sign_extend":
				case "repeat":
				case "rotate_left":
				case "rotate_right": {
					// all optimized in getEncodedTerm()
					return;
				}
				case "bvudiv": {
					// b != 0 => e(t) * b + r = a
					// b != 0 => r < b
				}
				case "bvurem":
					// b != 0 => q * b + e(t) = a
					// b != 0 => e(t) < b
					// multiplication and addition without overflow in both cases
					division(appterm, conjunction, encTerm);
					return;
				default:
					throw new UnsupportedOperationException(
							"Unsupported functionsymbol for bitblasting: " + fsym.getName());
				}
				for (int i = 0; i < conjunction.length; i++) {
					if (mBoolAtoms.containsKey(conjunction[i])) {
						final Literal conj = getLiteral(conjunction[i]);
						final Literal encT = getLiteral(encTerm[i]);
						final Literal[] lit1 = { conj.negate(), encT };
						addClause(lit1);
						final Literal[] lit2 = { conj, encT.negate() };
						addClause(lit2);
					} else {// TODO shift result uses this
						toClauses(mTheory.or(mTheory.not(conjunction[i]), encTerm[i]));
						toClauses(mTheory.or(mTheory.not(encTerm[i]), conjunction[i]));
					}
				}
			}
		} else {
			throw new UnsupportedOperationException("Unknown BVConstraint for term: " + term);
		}
	}

	/*
	 * Creates the Division and Remainder constraints. Adds the clauses of these constraints to the output clauses
	 * The return values of adder and multiplier are auxVars, no need to create additional auxVars here.
	 * This method can be used to encode bvudiv and bvurem.
	 * TODO needs optimization
	 */
	private void division(final ApplicationTerm appterm, final Term[] conjunction, final Term[] encTerm) {
		final FunctionSymbol fsym = appterm.getFunction();
		final Term[] encA = mEncTerms.get(appterm.getParameters()[0]);
		final Term[] encB = mEncTerms.get(appterm.getParameters()[1]);
		final int stage =
				mTheory.toNumeral(appterm.getParameters()[1].getSort().getIndices()[0]).intValue() - 1;
		final Term[] remainder;
		final Term[] product;
		if (fsym.getName().equals("bvudiv")) {
			remainder = createBoolVarArray(conjunction.length);
			product = multiplier(encTerm, encB, stage, null, false);
		} else if (fsym.getName().equals("bvurem")) {
			remainder = encTerm;
			product = multiplier(createBoolVarArray(conjunction.length), encB, stage, null, false);
		} else {
			throw new UnsupportedOperationException(
					"Unsupported functionsymbol for bitblasting: " + fsym.getName());
		}

		final Term[] sum = adder(product, remainder, mTheory.mFalse, null, false).getFirst();

		// Term lhs = (encB != False);
		final Term lhs = mTheory.or(encB);
		final Term bvult =
				mTheory.not(adder(remainder, negate(encB), mTheory.mTrue, null).getSecond());
		for (int i = 0; i < conjunction.length; i++) {
			conjunction[i] = mTheory.and(
					mTheory.or(mTheory.not(sum[i]), encA[i]),
					mTheory.or(mTheory.not(encA[i]), sum[i]));
		}

		// divisionConstraint:
		final Term divisionConstraint = mTheory.or(mTheory.not(lhs), mTheory.and(conjunction));
		toClauses(divisionConstraint);

		// remainderConstraint:
		final Term remainderConstraint = mTheory.or(mTheory.not(lhs), bvult);
		toClauses(remainderConstraint);

		if (fsym.getName().equals("bvudiv")) {
			// divZero Constraint:
			final Term divZero = mTheory.or(lhs, mTheory.and(encTerm));
			toClauses(divZero);
		} else if (fsym.getName().equals("bvurem")) {
			// remZero Constraint:
			final Term[] conjZero = new Term[encTerm.length];
			for (int i = 0; i < encTerm.length; i++) {
				conjZero[i] = mTheory.and(
						mTheory.or(mTheory.not(encTerm[i]), encA[i]),
						mTheory.or(mTheory.not(encA[i]), encTerm[i]));
			}
			final Term divZero = mTheory.or(lhs, mTheory.and(conjZero));
			toClauses(divZero);
		} else {
			throw new UnsupportedOperationException(
					"Unsupported functionsymbol for bitblasting: " + fsym.getName());
		}

	}

	/*
	 * Concationation on the encoded terms(Array of Bools).
	 * On Terms: 00 concat 01 = 0001
	 * As Array: [0 0] concat [1 0] = [1 0 0 0]
	 */
	private Term[] concatArrays(final Term[] b, final Term[] a) {
		final Term[] result = Arrays.copyOf(a, a.length + b.length);
		System.arraycopy(b, 0, result, a.length, b.length);
		return result;
	}

	// negates each term in terms array
	private Term[] negate(final Term[] terms) {
		final Term[] negateresult = new Term[terms.length];
		for (int i = 0; i < terms.length; i++) {
			negateresult[i] = mTheory.not(terms[i]);
		}
		return negateresult;
	}

	/*
	 * returns an AuxVar representing (a xor b xor cin). Clauses for this auxvar will be created and saved directly.
	 * cin and a can be false.
	 * If encAdd is null, the adder is not called to encode bvadd, bvsub..., but as part of the multiplier.
	 * an additional auxvar as result needs to be created then.
	 */
	private Term sumAdder(final Term aTerm, final Term bTerm, final Term cin, final Term encAdd) {
		final Literal b = getLiteral(bTerm);

		final Literal at;
		Term result;
		if (encAdd == null) { // adder was called by multiplier or similar functions
			final Term boolVar = createBoolAtom(null);
			at = getLiteral(boolVar);
			result = boolVar;
		} else {
			at = getLiteral(encAdd);
			result = encAdd;
		}

		if (cin.equals(mTheory.mFalse)) {
			if (aTerm.equals(mTheory.mFalse)) {
				final Literal[] lit2 = { at, b.negate() };
				addClause(lit2);
				final Literal[] lit3 = { at.negate(), b };
				addClause(lit3);
			} else {
				final Literal a = getLiteral(aTerm);
				final Literal[] lit2 = { at, a, b.negate() };
				addClause(lit2);
				final Literal[] lit4 = { at, a.negate(), b, };
				addClause(lit4);
				final Literal[] lit6 = { at.negate(), a, b, };
				addClause(lit6);
				final Literal[] lit7 = { at.negate(), a.negate(), b.negate() };
				addClause(lit7);
			}
		} else if (cin.equals(mTheory.mTrue)) {
			if (aTerm.equals(mTheory.mFalse)) {
				final Literal[] lit2 = { at, b };
				addClause(lit2);
				final Literal[] lit3 = { at.negate(), b.negate() };
				addClause(lit3);
			} else {
				final Literal a = getLiteral(aTerm);
				final Literal[] lit2 = { at.negate(), a, b.negate() };
				addClause(lit2);
				final Literal[] lit4 = { at.negate(), a.negate(), b, };
				addClause(lit4);
				final Literal[] lit6 = { at, a, b, };
				addClause(lit6);
				final Literal[] lit7 = { at, a.negate(), b.negate() };
				addClause(lit7);
			}
		} else {
			final Literal c = getLiteral(cin);

			if (aTerm.equals(mTheory.mFalse)) {
				final Literal[] lit2 = { at, c, b.negate() };
				addClause(lit2);
				final Literal[] lit4 = { at, c.negate(), b, };
				addClause(lit4);
				final Literal[] lit6 = { at.negate(), c, b, };
				addClause(lit6);
				final Literal[] lit7 = { at.negate(), c.negate(), b.negate() };
				addClause(lit7);

			} else {
				final Literal a = getLiteral(aTerm);
				final Literal[] lit1 = { at, a.negate(), b.negate(), c.negate() };
				addClause(lit1);
				final Literal[] lit2 = { at, a, b.negate(), c };
				addClause(lit2);
				final Literal[] lit3 = { at, a, b, c.negate() };
				addClause(lit3);
				final Literal[] lit4 = { at, a.negate(), b, c };
				addClause(lit4);

				final Literal[] lit5 = { at.negate(), a, b.negate(), c.negate() };
				addClause(lit5);
				final Literal[] lit6 = { at.negate(), a, b, c };
				addClause(lit6);
				final Literal[] lit7 = { at.negate(), a.negate(), b.negate(), c };
				addClause(lit7);
				final Literal[] lit8 = { at.negate(), a.negate(), b, c.negate() };
				addClause(lit8);
			}
		}
		return result;
	}

	/*
	 * returns an AuxVar representing ((a and b) or (mTheory.(a xor b) and cin)). Clauses for this auxvar will be
	 * created and saved directly.
	 * cin and a can be false.
	 */
	private Term carryAdder(final Term aTerm, final Term bTerm, final Term cin) {
		if (aTerm.equals(mTheory.mFalse)) {
			final Term carryResult = createBoolAtom(null);
			final Literal crlit = getLiteral(carryResult);
			final Literal b = getLiteral(bTerm);
			final Literal[] lit1 = { crlit.negate(), b };
			addClause(lit1);
			if (!cin.equals(mTheory.mFalse)) {
				final Literal c = getLiteral(cin);
				final Literal[] lit2 = { crlit.negate(), c };
				addClause(lit2);
				final Literal[] lit3 = { crlit, c.negate(), b.negate() };
				addClause(lit3);
			} else {
				final Literal[] lit2 = { crlit.negate() };
				addClause(lit2);
				final Literal[] lit3 = { crlit, b.negate() };
				addClause(lit3);
			}
			return carryResult; // createAuxVar(mTheory.and(bTerm, cin))
		}
		if (cin.equals(mTheory.mFalse)) {
			final Term carryResult = createBoolAtom(null);
			final Literal crlit = getLiteral(carryResult);
			final Literal a = getLiteral(aTerm);
			final Literal b = getLiteral(bTerm);
			final Literal[] lit1 = { crlit.negate(), a };
			addClause(lit1);
			final Literal[] lit2 = { crlit.negate(), b };
			addClause(lit2);
			final Literal[] lit3 = { crlit, a.negate(), b.negate() };
			addClause(lit3);
			return carryResult; // createAuxVar(mTheory.and(aTerm, bTerm));
		} else if (cin.equals(mTheory.mTrue)) {
			final Term carryResult = createBoolAtom(null);
			final Literal crlit = getLiteral(carryResult);
			final Literal a = getLiteral(aTerm);
			final Literal b = getLiteral(bTerm);
			final Literal[] lit1 = { crlit, a.negate() };
			addClause(lit1);
			final Literal[] lit2 = { crlit, b.negate() };
			addClause(lit2);
			final Literal[] lit3 = { crlit.negate(), a, b };
			addClause(lit3);
			return carryResult; // createAuxVar(mTheory.or(aTerm, bTerm));
		} else {
			// return mTheory.and(mTheory.or(aTerm, bTerm), mTheory.or(aTerm, cin), mTheory.or(bTerm, cin));
			final Literal a = getLiteral(aTerm);
			final Literal b = getLiteral(bTerm);
			final Literal c = getLiteral(cin);

			final Term boolVar = createBoolAtom(null);

			final Literal auxVar = getLiteral(boolVar);

			final Literal[] lit1 = { auxVar, a.negate(), b.negate() };
			addClause(lit1);
			final Literal[] lit2 = { auxVar, a.negate(), c.negate() };
			addClause(lit2);
			final Literal[] lit3 = { auxVar, b.negate(), c.negate() };
			addClause(lit3);

			final Literal[] lit4 = { auxVar.negate(), b, a };
			addClause(lit4);
			final Literal[] lit5 = { auxVar.negate(), a, c };
			addClause(lit5);
			final Literal[] lit6 = { auxVar.negate(), b, c };
			addClause(lit6);

			return boolVar;
		}
	}



	private Term[] carryBits(final Term[] encA, final Term[] encB, final Term cin) {
		assert encA.length == encB.length;
		final Term[] carryBits = new Term[encA.length + 1];
		carryBits[0] = cin;
		for (int i = 1; i <= encA.length; i++) {
			carryBits[i] = carryAdder(encA[i - 1], encB[i - 1], carryBits[i - 1]);

		}
		return carryBits;
	}

	/**
	 * default adder, with overflow enabled
	 **/
	private Pair<Term[], Term> adder(final Term[] encA, final Term[] encB, final Term cin, final Term[] encAdd) {
		return adder(encA, encB, cin, encAdd, true);
	}

	/*
	 * Full Adder.
	 * No recursion, instead we use auxvars.
	 * if overflow is false (used in division) cout needs to be false
	 */
	private Pair<Term[], Term> adder(final Term[] encA, final Term[] encB, final Term cin, final Term[] encAdd,
			final boolean overflow) {
		assert encA.length == encB.length;
		final Term[] sumResult = new Term[encA.length];
		final Term[] carryBits = carryBits(encA, encB, cin);
		for (int i = 0; i < encA.length; i++) {
			if (mClausifier.getEngine().isTerminationRequested()) {
				break;
			}
			if (encAdd != null) {
				// will create the clauses directly
				sumResult[i] = sumAdder(encA[i], encB[i], carryBits[i], encAdd[i]);
			} else {
				// won't create clauses, used in the multiplier etc.
				sumResult[i] = sumAdder(encA[i], encB[i], carryBits[i], null);
			}
		}
		final Term cout = carryBits[carryBits.length - 1];
		if (!overflow) { //used for division constraints
			if (cout.equals(mTheory.mFalse)) {
				return new Pair<>(sumResult, cout);
			} else {
				final Literal coutLit = getLiteral(cout);
				final Literal[] lit = { coutLit.negate() };
				addClause(lit);
			}
		}
		return new Pair<>(sumResult, cout);
	}

	private Term createBoolAtom(String name) {
		if (name == null) {
			name = "AuxVar";
		}
		final TermVariable boolVar = mTheory.createFreshTermVariable(name, mTheory.getSort("Bool"));
		final DPLLAtom dpll = new BooleanVarAtom(boolVar, mStackLevel);
		mBoolAtoms.put(boolVar, dpll);
		return boolVar;
	}

	// create all auxiliary variables, needed to get rid of recursions
	private Term[][] createBoolVarMap(final int stage, final int indices) {
		final Term[][] boolvarmap = new Term[stage][indices];
		for (int s = 0; s < stage; s++) {
			for (int i = 0; i < indices; i++) {
				final String stageRec = "rec_" + i + "_" + s;
				final Term boolVar = createBoolAtom(stageRec);
				boolvarmap[s][i] = boolVar;
			}
		}
		return boolvarmap;
	}


	// create all bool variables representing a bitvector
	private Term[] createBoolVarArray(final int indices) {
		final Term[] boolvarArray = new Term[indices];
		for (int i = 0; i < indices; i++) {
			final String stageRec = "aux_" + i;
			final Term boolVar = createBoolAtom(stageRec);
			boolvarArray[i] = boolVar;
		}

		return boolvarArray;
	}


	/*
	 * Check if a auxvar helps in the cnf process
	 * If (appterm.getParameters().length > 1), create auxvar and add it to cnf
	 * Else return input
	 */
	private Term createAuxVar(final Term represented) {
		if (represented instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) represented;
			if (appterm.getParameters().length > 1) { // Maybe only worth, if appterm is a conjunction
				final Term boolVar = createBoolAtom(null);
				toClauses(mTheory.and(mTheory.or(mTheory.not(boolVar), represented),
						mTheory.or(mTheory.not(represented), boolVar)));
				return boolVar;
			}
		}
		//Probably not worth to add the Aux Var
		return represented;
	}


	/*
	 * Barrel Shifter
	 * Optimization: a<<b = ite(b3 \/ b4, (0,0,0,0), ls(a,b, log_2(length a) - 1))
	 * leftshift, true if bvshl. False if bvlshr
	 * No recursion, instead we use auxvars.
	 */
	private Term[] shift(final Term a, final Term b, int stage, final boolean leftshift) {

		final Term[] encA = mEncTerms.get(a);
		final Term[] encB = mEncTerms.get(b);
		final Term[] shiftResult = new Term[encA.length];

		// Log Base 2, rounded up
		final int logTwo = (int) Math.ceil((float) (Math.log(encA.length) / Math.log(2)));
		final Term[][] boolvarmap = createBoolVarMap(logTwo, encA.length);
		// if any enB[x] with x > log_2(encA.length) is true, then shift result is zero BitVec
		for (int i = 0; i < encA.length; i++) {
			final List<Term> disj = new ArrayList<>();
			for (int k = logTwo; k < encB.length; k++) {
				disj.add(encB[k]);
			}
			final Term disjunction = listToDisjunction(disj, false);
			shiftResult[i] = mTheory.and(mTheory.or(mTheory.not(disjunction), mTheory.mFalse),
					mTheory.or(mTheory.or(disjunction), boolvarmap[logTwo - 1][i]));
		}
		// Only consider stages smaller than maximal shift distance
		stage = logTwo;
		for (int s = 0; s < stage; s++) {
			if (mClausifier.getEngine().isTerminationRequested()) {
				break;
			}
			for (int i = 0; i < encA.length; i++) {
				if (mClausifier.getEngine().isTerminationRequested()) {
					break;
				}
				final int pow = (int) Math.pow(2, s);
				final Term ifTerm;
				final Term elseTerm;
				Term thenTerm;
				if (s == 0) {
					ifTerm = encB[0];
					elseTerm = encA[i];
					// rightshift
					if ((i + pow < encA.length) && !leftshift) {
						thenTerm = encA[i + pow];
						// leftshift
					} else if (i >= pow && leftshift) {
						thenTerm = encA[i - pow];
						// no shift
					} else {
						thenTerm = mTheory.mFalse;
					}
					// ifthenelse in CNF (not a or b) and (a or c)
				} else {
					ifTerm = encB[s];
					elseTerm = boolvarmap[s - 1][i];
					if ((i + pow < encA.length) && !leftshift) {
						thenTerm = boolvarmap[s - 1][i + pow];
					} else if (i >= pow && leftshift) {
						thenTerm = boolvarmap[s - 1][i - pow];
					} else {
						thenTerm = mTheory.mFalse;
					}
				}
				// Add Auxiliary variables and their represented term (ifte), as clauses
				toClausesIte(boolvarmap[s][i], ifTerm, thenTerm, elseTerm);
			}
		}
		return shiftResult;
	}

	/*
	 * get's a list of terms,
	 * returns these terms as disjunction
	 * if negated is set to true, each disjunct will be negated
	 */
	private Term listToDisjunction(final List<Term> list, final boolean negate) {
		assert !list.isEmpty();
		Term[] disjArray = new Term[list.size()];
		disjArray = list.toArray(disjArray);
		for (int i = 0; i < list.size(); i++) {
			if (negate) {
				disjArray = negate(disjArray);
			}
		}
		return mTheory.or(disjArray);
	}

	/*
	 * Used, when b is not a term in the original formula, therefore mEncTerms.get(b) would be null
	 * No need for AuxVars since we can calculate the actual shift result.
	 * Used in the multiplier
	 */
	private Term[] leftshiftMul(final Term[] encA, final String b, final int stage) {
		final Term[] shiftResult = new Term[encA.length];
		if (stage == -1) {
			return encA;
		} else {
			for (int i = 0; i < encA.length; i++) {

				if (b.charAt(b.length() - 1 - stage) == '1') {
					if (i >= Math.pow(2, stage)) {
						shiftResult[i] =
								leftshiftMul(encA, b, stage - 1)[i - (int) Math.pow(2, stage)];
					} else {
						shiftResult[i] = mTheory.mFalse;
					}
				} else {
					shiftResult[i] = leftshiftMul(encA, b, stage - 1)[i];
				}
			}
		}

		return shiftResult;
	}

	private Term[] multiplier(final Term a, final Term b, final int stage, final Term[] encMul) {
		final Term[] encA = mEncTerms.get(a);
		final Term[] encB = mEncTerms.get(b);
		return multiplier(encA, encB, stage, encMul, true);
	}

	/*
	 * Multiplier without recursion. Instead we use aux vars.
	 * returns null, if encMul was given. Then clauses will be created during the process
	 * if overflow is false, all carry out bits from the adder need to be false (used for division constraints)
	 */
	private Term[] multiplier(final Term[] encA, final Term[] encB, final int stage, final Term[] encMul,
			final boolean overflow) {
		final int size = encA.length;
		final Term[] zeroVec = new Term[size];
		Arrays.fill(zeroVec, mTheory.mFalse);
		final Term[][] boolvarmap = createBoolVarMap(stage + 1, encA.length);
		if (stage == 0) {
			if (encMul == null) {
				return zeroVec;
			} else {
				for (int i = 0; i < size; i++) {
					final Literal result = getLiteral(encMul[i]);
					final Literal[] lit = { result.negate() };
					addClause(lit);
				}
				return null;
			}
		}
		// Create AuxVars for each, except last.
		for (int s = 0; s < stage; s++) {
			final Term[] mul;
			final Term[] shift;
			if (s == 0) {
				mul = zeroVec;
				shift = encA;
			} else {
				// Auxiliary Variable
				mul = boolvarmap[s - 1];
				String SAsString = Integer.toString(s, 2);
				SAsString = new String(new char[size - SAsString.length()]).replace("\0", "0") + SAsString;
				shift = leftshiftMul(encA, SAsString, size - 1);
			}
			final Term[] ifte = new Term[size];
			for (int i = 0; i < size; i++) {
				if (mClausifier.getEngine().isTerminationRequested()) {
					break;
				}

				ifte[i] = createBoolAtom(null);
				if (shift[i].equals(mTheory.mFalse)) {
					final Literal iteFalse = getLiteral(ifte[i]);
					final Literal[] lit = { iteFalse.negate() };
					addClause(lit);
				} else {
					// if encB(s) then shift[i], else mTheory.mFalse
					toClausesIte(ifte[i], encB[s], shift[i], mTheory.mFalse);
				}

				if (!overflow && i + s > stage) {// used for division constraints
					final Term of = mTheory.not(mTheory.and(encA[i], encB[s]));
					// encA[i + s] must be false
					toClauses(of);
				}

			}
			if (mClausifier.getEngine().isTerminationRequested()) {
				break;
			}
			adder(mul, ifte, mTheory.mFalse, boolvarmap[s], overflow).getFirst();

		}
		// Last stage
		final Term[] shift;
		// stage must not be 0 at this point!
		String SAsString = Integer.toString(stage, 2);
		SAsString = new String(new char[size - SAsString.length()]).replace("\0", "0") + SAsString;
		shift = leftshiftMul(encA, SAsString, size - 1);

		final Term[] ifte = new Term[size];
		for (int i = 0; i < size; i++) {
			ifte[i] = createBoolAtom(null);
			if (shift[i].equals(mTheory.mFalse)) {
				final Literal iteFalse = getLiteral(ifte[i]);
				final Literal[] lit = { iteFalse.negate() };
				addClause(lit);
			} else {
				// if encB(stage) then shift[i], else mTheory.mFalse
				toClausesIte(ifte[i], encB[stage], shift[i], mTheory.mFalse);
			}
			if (!overflow && i > 0) {// used for division constraints
				final Term overflo = mTheory.not(mTheory.and(encA[i], encB[stage]));
				toClauses(overflo);
			}
		}
		if (mClausifier.getEngine().isTerminationRequested()) {
			return null;
		}
		final Term[] sum = adder(boolvarmap[stage - 1], ifte, mTheory.mFalse, encMul, overflow).getFirst();
		if (encMul == null) {
			return sum;
		} else {
			return null;
		}
	}


	/*
	 * Transforms the term into Cnf and collects the clauses.
	 * Inefficient, try calculate the clauses directly.
	 */
	private void toClauses(final Term term) {
		final CleanTransfomer cleaner = new CleanTransfomer();
		final NnfTransformer nnf = new NnfTransformer();
		final Term nnfTerm = nnf.transform(term);
		final CnfTransformer cnf = new CnfTransformer();
		final Term cnfTerm = cnf.transform(cnf.transform(nnfTerm));
		final Term cleanTerm = cleaner.transform(cnfTerm);
		if (cleanTerm instanceof ApplicationTerm) {
			final ApplicationTerm appClean = (ApplicationTerm) cleanTerm;
			if (appClean.getFunction().getName().equals("and")) {
				for (int i = 0; i < appClean.getParameters().length; i++) {
					addClauses(appClean.getParameters()[i]);
				}
				return;
			}
		}
		addClauses(cleanTerm);

	}


	/*
	 * Creates the clauses for (boolVar <=> ite) directly and adds them to the bitblasting result.
	 * Ensure that there exists a literal for each argument.
	 * thenTerm can be false
	 */
	private void toClausesIte(final Term atom, final Term ifTerm, final Term thenTerm, final Term elseTerm) {
		assert ifTerm != mTheory.mFalse;
		final Literal atomlit = getLiteral(atom);
		final Literal ifLit = getLiteral(ifTerm);
		if (elseTerm.equals(mTheory.mFalse)) {
			assert !thenTerm.equals(mTheory.mFalse);
			final Literal thenLit = getLiteral(thenTerm);
			final Literal[] lit1 = { atomlit, ifLit.negate(), thenLit.negate() };
			addClause(lit1);
			final Literal[] lit2 = { atomlit.negate(), ifLit };
			addClause(lit2);
			final Literal[] lit3 = { atomlit.negate(), ifLit.negate(), thenLit };
			addClause(lit3);
			final Literal[] lit5 = { atomlit, ifLit.negate(), ifLit };
			addClause(lit5);
			return;
		}
		final Literal elseLit = getLiteral(elseTerm);
		if (!thenTerm.equals(mTheory.mFalse)) {
			final Literal thenLit = getLiteral(thenTerm);
			final Literal[] lit1 = { atomlit, ifLit.negate(), thenLit.negate() };
			addClause(lit1);
			final Literal[] lit2 = { atomlit.negate(), ifLit, elseLit };
			addClause(lit2);
			final Literal[] lit3 = { atomlit.negate(), ifLit.negate(), thenLit };
			addClause(lit3);
			final Literal[] lit4 = { atomlit, elseLit.negate(), elseLit };
			addClause(lit4);
		} else {
			// thenTerm = mTheory.mFalse;
			final Literal[] lit1 = { atomlit.negate(), ifLit, elseLit };
			addClause(lit1);
			final Literal[] lit2 = { atomlit.negate(), ifLit.negate() };
			addClause(lit2);
		}
		final Literal[] lit5 = { atomlit, ifLit.negate(), ifLit };
		addClause(lit5);
		final Literal[] lit6 = { atomlit, ifLit, elseLit.negate() };
		addClause(lit6);

	}

	/**
	 * returns the literal used to encode the input term
	 */
	public Literal getLiteral(final Term term) {
		if(term instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) term;
			final FunctionSymbol fsym = appterm.getFunction();
			if (fsym.getName().equals("not")) {
				assert mBoolAtoms.containsKey(appterm.getParameters()[0]);
				return mBoolAtoms.get(appterm.getParameters()[0]).negate();
			}
		}
		assert mBoolAtoms.containsKey(term);
		return mBoolAtoms.get(term);
	}

	private void addClause(final Literal[] literal) {
		assert !(literal.length == 0);
		if (literal[0].getSMTFormula(mTheory).equals(mTheory.mTrue) && literal.length == 1) {
			return;
		}
		final Clause cl = new Clause(literal, mStackLevel);
		cl.setProof(new LeafNode(-1, SourceAnnotation.EMPTY_SOURCE_ANNOT));
		mClauses.add(cl);
	}

	/*
	 * adds the clauses of term to the Bitblasting result.
	 * term must be a disjunction or literal.
	 */
	private void addClauses(final Term term) {
		assert !term.equals(mTheory.mFalse);
		if (term.equals(mTheory.mTrue)) {
			return;
		}
		final ArrayList<Literal> literals = new ArrayList<>();
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) term;
			final FunctionSymbol fsym = appterm.getFunction();
			if (fsym.getName().equals("or")) {
				for (int i = 0; i < appterm.getParameters().length; i++) {
					literals.add(getLiteral(appterm.getParameters()[i]));
				}
			} else if (fsym.getName().equals("true")) {
				literals.add(new TrueAtom());
			} else {
				literals.add(getLiteral(term));
			}
		} else {
			literals.add(getLiteral(term));
		}

		final Clause cl = new Clause(literals.toArray(new Literal[literals.size()]), mStackLevel);
		cl.setProof(new LeafNode(-1, SourceAnnotation.EMPTY_SOURCE_ANNOT));
		mClauses.add(cl);
	}

	/**
	 * returns all atoms used as encoding.
	 */
	public Collection<DPLLAtom> getBoolAtoms() {
		return mBoolAtoms.values();
	}

	/**
	 * used to get the Bitblasting result
	 **/
	public ScopedArrayList<Clause> getClauses() {
		return mClauses;
	}

	/**
	 * negates the input literals, used to create a conflict clause
	 **/
	public Literal[] getNegatedInputLiterals() {
		final Literal[] lit = new Literal[mInputLiterals.size()];
		for (int i = 0; i < mInputLiterals.size(); i++) {
			lit[i] = mInputLiterals.get(i).negate();
		}
		return lit;
	}

	/**
	 * returns the map, encoded Atom to Input Literal
	 */
	public HashMap<Term, Literal> getLiteralMap() {
		return mLiterals;
	}
}