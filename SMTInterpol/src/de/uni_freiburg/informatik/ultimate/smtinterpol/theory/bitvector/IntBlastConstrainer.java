
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

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinArSolve;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffineTerm;

public class IntBlastConstrainer {
	private final Theory mTheory;
	private FunctionSymbol mIntand;

	public enum ConstraintsForBitwiseOperations {
		/**
		 * Precise "sum" constraints for bit-wise-and
		 */
		SUM,
		/**
		 * Precise "bit-wise" constraints for bit-wise-and
		 */
		BITWISE,
		/**
		 * Overapproximation of bit-wise-and by lazy constraints
		 */
		LAZY,
		/**
		 * Overapproximation of all bit-wise functions by auxiliary variables
		 */
		NONE
		/**
		 * Overapproximation of all bit-wise functions by uninterpreted function symbol
		 */
	}

	public final ConstraintsForBitwiseOperations mMode;

	private final HashSet<Term> mConstraintSet; // Set of all constraints
	private final HashSet<Literal> mLaVarBoundSet;
	private final HashSet<Term> mTvConstraintSet; // Set of all constraints for quantified variables
	private final Clausifier mClausifier;
	private final LinArSolve mIntSolver;
	/*
	 * This Class contains of the methods to create constraints for the translation of bit-wise-AND and variables.
	 * The constraints for uninterpreted constants and bit-wise-AND can be accessed via getConstraints().
	 * The constraints for TermVariables can be accessed via getTvConstraints().
	 */
	public IntBlastConstrainer(final Theory theory, final ConstraintsForBitwiseOperations mode,
			final Clausifier clausifier, final LinArSolve intSolver) {
		mTheory = theory;
		mMode = mode;
		mClausifier = clausifier;
		mIntSolver = intSolver;
		mConstraintSet = new HashSet<>();
		mTvConstraintSet = new HashSet<>();
		mLaVarBoundSet = new HashSet<>();
		// mTranslatedTerms = new HashMap<>();
		// mReversedTranslationMap = new HashMap<>();

		final Sort intSort = mTheory.getNumericSort();
		final Sort[] functionsort = new Sort[2];
		functionsort[0] = intSort;
		functionsort[1] = intSort;

		// if (mIntand == null) {
		// if (mTheory.getFunctionSymbol("intand") == null) {
		// mTheory.declareFunction("intand", functionsort, intSort);
		// }
		// mIntand = mTheory.getFunctionSymbol("intand");
		// }
	}

	// returns the Set of constraints for uninterpreted constants and bit-wise-AND
	public HashSet<Term> getConstraints() {
		return mConstraintSet;
	}

	// returns the Set of constraints for TermVariables
	public HashSet<Term> getTvConstraints() {
		return mTvConstraintSet;
	}

	public FunctionSymbol getIntAndFunctionSymbol() {
		return mIntand;
	}

	private Term getLowerVarBounds(final Term bvterm, final Term intTerm) {
		final Sort intSort = mTheory.getNumericSort();
		final Term translatedVar = intTerm;
		final Term lowerBound = mTheory.term("<=", Rational.ZERO.toTerm(intSort), translatedVar);
		return lowerBound;
	}

	private Term getUpperVarBounds(final Term bvterm, final Term intTerm) {
		final Sort intSort = mTheory.getNumericSort();
		final int width = Integer.valueOf(bvterm.getSort().getIndices()[0]);

		final Term translatedVar = intTerm;
		final Rational twoPowWidth = Rational.valueOf(BigInteger.valueOf(2).pow(width), BigInteger.ONE);
		final Rational twoPowWidthSubOne = twoPowWidth.sub(Rational.ONE);
		// Strict upper Bound
		final Term upperBoundPaper =
				mTheory.term("<", translatedVar, mTheory.rational(twoPowWidth, intSort));
		final Term upperBound =
				mTheory.term("<=", translatedVar, mTheory.rational(twoPowWidthSubOne, intSort));
		return upperBoundPaper;
	}

	public void varLaBounds(final Term bvVar, final Term intVar) {
		final Sort intSort = mTheory.getNumericSort();
		final int width = Integer.valueOf(bvVar.getSort().getIndices()[0]);
		final Term translatedVar = intVar;
		final Rational twoPowWidth = Rational.valueOf(BigInteger.valueOf(2).pow(width), BigInteger.ONE);


		// mTheory.term("<=", Rational.ZERO.toTerm(intSort), translatedVar)

		final boolean strictLowerBound = false;
		final SMTAffineTerm lowerBoundAt = SMTAffineTerm.create(mTheory.term("-", intVar));
		final MutableAffineTerm lowerMat =
				mClausifier.createMutableAffinTerm(lowerBoundAt, SourceAnnotation.EMPTY_SOURCE_ANNOT);

		final Literal lowerConstraintLiteral = mIntSolver.generateConstraint(lowerMat, strictLowerBound);





		final boolean strictUpperBound = false;
		final SMTAffineTerm upperBoundAt = SMTAffineTerm.create(mTheory.term("-", intVar,
				mTheory.rational(twoPowWidth.sub(Rational.ONE), intSort)));
		final MutableAffineTerm upperMat =
				mClausifier.createMutableAffinTerm(upperBoundAt, SourceAnnotation.EMPTY_SOURCE_ANNOT);

		final Literal upperConstraintLiteral = mIntSolver.generateConstraint(upperMat, strictUpperBound);

		mLaVarBoundSet.add(lowerConstraintLiteral);
		mLaVarBoundSet.add(upperConstraintLiteral);
	}

	public void varConstraint(final Term bvterm, final Term intTerm) {
		//auch in clausifier eager, 
		
		mConstraintSet.add(getLowerVarBounds(bvterm, intTerm));
		mConstraintSet.add(getUpperVarBounds(bvterm, intTerm));
	}

	public Term getTvConstraint(final TermVariable bvterm, final Term intTerm) {
		final Term lowerBound = getLowerVarBounds(bvterm, intTerm);
		final Term upperBoundPaper = getUpperVarBounds(bvterm, intTerm);
		mTvConstraintSet.add(lowerBound);
		mTvConstraintSet.add(upperBoundPaper);
		return mTheory.term("and", lowerBound, upperBoundPaper);
	}

	// returns bounds for select terms, they are not added to the sets.
	public Term getSelectConstraint(final Term bvterm, final Term intTerm) {
		final Term lowerBound = getLowerVarBounds(bvterm, intTerm);
		final Term upperBoundPaper = getUpperVarBounds(bvterm, intTerm);
		return mTheory.term("and", lowerBound, upperBoundPaper);
	}

	/**
	 *
	 * @return true iff the constraints define only an overapproximation of
	 *         bvand.
	 */
	public boolean bvandConstraint(final Term intTerm, final int width) {
		//eager in clausifier, lazy in theroy solver, intand im termcompiler hinzufügen
		//
		if (mMode.equals(ConstraintsForBitwiseOperations.NONE)) {
			return true;
		}
		final Sort intSort = mTheory.getNumericSort();
		if (!intTerm.getSort().isNumericSort()) {
			throw new UnsupportedOperationException("Cannot create Constraints vor non-Int Sort Terms");
		}
		if (intTerm instanceof ApplicationTerm) {
			final ApplicationTerm apterm = (ApplicationTerm) intTerm;
			final Term translatedLHS = apterm.getParameters()[0];
			final Term translatedRHS = apterm.getParameters()[1];

			final Rational twoPowWidth = Rational.valueOf(BigInteger.valueOf(2).pow(width), BigInteger.ONE);

			final Term modeConstraint;
			Term lazy = mTheory.term("true");
			switch (mMode) {
			case SUM: {
				modeConstraint = bvandSUMConstraints(width, translatedLHS, translatedRHS);
				break;
			}
			case BITWISE: {
				final Term lowerBound = mTheory.term("<=", Rational.ZERO.toTerm(intSort), apterm);
				final Term upperBound =
						mTheory.term("<", apterm, mTheory.rational(twoPowWidth, intSort));
				mConstraintSet.add(lowerBound);
				mConstraintSet.add(upperBound);
				modeConstraint = bvandBITWISEConstraints(width, translatedLHS, translatedRHS);
				break;
			}
			case LAZY: {
				final Term lowerBound = mTheory.term("<=", Rational.ZERO.toTerm(intSort), apterm);
				final Term upperBound =
						mTheory.term("<", apterm, mTheory.rational(twoPowWidth, intSort));
				lazy = bvandLAZYConstraints(width, translatedLHS, translatedRHS);
				mConstraintSet.add(lowerBound);
				mConstraintSet.add(upperBound);
				mConstraintSet.add(lazy);
				return true;
			}

			case NONE: {
				throw new UnsupportedOperationException("Deal with this mode at the beginning of this method");
			}
			default: {
				throw new UnsupportedOperationException("Set Mode for bvand Constraints");
			}
			}

			// Important, to match with the backtranslation we also need to bring it in the same form here

			mConstraintSet.add(modeConstraint);
			return false;
		}
		throw new AssertionError("method must be called on IntAnd");
	}

	private Term bvandSUMConstraints(final int width, final Term translatedLHS, final Term translatedRHS) {
		final Sort intSort = mTheory.getNumericSort();
		final BigInteger two = BigInteger.valueOf(2);
		final Term[] sum = new Term[width];
		for (int i = 0; i < width; i++) { // width + 1?
			final Term twoPowI = mTheory.rational(Rational.valueOf(two.pow(i), BigInteger.ONE), intSort);
			final Term one = mTheory.rational(Rational.ONE, intSort);
			final Term zero = mTheory.rational(Rational.ZERO, intSort);
			final Term ite = mTheory.term("ite", mTheory.term("=", isel(i, translatedLHS), isel(i, translatedRHS), one),
					one, zero);
			final Term mul = mTheory.term("*", twoPowI, ite);
			sum[i] = mul;
		}
		return mTheory.term("=", mTheory.term(mIntand.getName(), translatedLHS, translatedRHS), mTheory.term("+", sum));
	}

	private Term bvandBITWISEConstraints(final int width, final Term translatedLHS, final Term translatedRHS) {
		final Sort intSort = mTheory.getNumericSort();
		final Term[] and = new Term[width];
		for (int i = 0; i < width; i++) {
			final Term one = mTheory.rational(Rational.ONE, intSort);
			final Term zero = mTheory.rational(Rational.ZERO, intSort);
			final Term ite = mTheory.term("ite", mTheory.term("=", isel(i, translatedLHS), isel(i, translatedRHS), one),
					one, zero);
			final Term equals =
					mTheory.term("=", isel(i, mTheory.term(mIntand.getName(), translatedLHS, translatedRHS)), ite);
			and[i] = equals;
		}
		return mTheory.and(and);
	}

	private Term bvandLAZYConstraints(final int width, final Term translatedLHS, final Term translatedRHS) {
		final Sort intSort = mTheory.getNumericSort();
		final Term zero = mTheory.rational(Rational.ZERO, intSort);
		final Term maxNumber = mTheory.rational(
				Rational.valueOf(BigInteger.valueOf(2).pow(width), BigInteger.ONE), intSort);
		final Term[] lazyConstraints = new Term[8];
		final Term intand = mTheory.term(mIntand.getName(), translatedLHS, translatedRHS);
		// LHS upper Bound
		lazyConstraints[0] = mTheory.term("<=", intand, translatedLHS);
		// RHS upper Bound
		lazyConstraints[1] = mTheory.term("<=", intand, translatedRHS);
		// Idempotence
		lazyConstraints[2] = mTheory.term("=>", mTheory.term("=", translatedLHS, translatedRHS),
				mTheory.term("=", intand, translatedLHS));
		// Symmetry
		lazyConstraints[3] = mTheory.term("=", intand, mTheory.term(mIntand.getName(), translatedRHS, translatedLHS));
		// LHS Zero
		lazyConstraints[4] =
				mTheory.term("=>", mTheory.term("=", translatedLHS, zero), mTheory.term("=", intand, zero));
		// RHS Zero
		lazyConstraints[5] =
				mTheory.term("=>", mTheory.term("=", zero, translatedRHS), mTheory.term("=", intand, zero));
		// LHS max number
		lazyConstraints[6] = mTheory.term("=>", mTheory.term("=", translatedLHS, maxNumber),
				mTheory.term("=", intand, translatedRHS));
		// RHS max number
		lazyConstraints[7] = mTheory.term("=>", mTheory.term("=", maxNumber, translatedRHS),
				mTheory.term("=", intand, translatedLHS));
		return mTheory.term("and", lazyConstraints);
	}

	// Term that picks the bit at position "i" of integer term "term" interpreted as binary
	private Term isel(final int i, final Term term) {
		final Sort intSort = mTheory.getNumericSort();
		final Term two =
				mTheory.rational(Rational.valueOf(BigInteger.valueOf(2), BigInteger.ONE), intSort);
		final Term twoPowI = mTheory.rational(
				Rational.valueOf(BigInteger.valueOf(2).pow(i), BigInteger.ONE), intSort);
		return mTheory.term("mod", mTheory.term("div", term, twoPowI), two);
	}
}