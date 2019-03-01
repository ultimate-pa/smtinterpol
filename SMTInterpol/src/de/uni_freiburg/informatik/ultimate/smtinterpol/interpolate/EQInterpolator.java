/*
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitesimalNumber;

/**
 * Class to interpolate Nelson-Oppen Theory combination lemmas. These lemmas propagate a CC equality to a LA equality or
 * vice versa.
 *
 * @author hoenicke
 *
 */
public class EQInterpolator {
	Interpolator mInterpolator;

	public EQInterpolator(final Interpolator interpolator) {
		mInterpolator = interpolator;
	}

	/**
	 * Convert this term to an InterpolatorAffineTerm
	 */
	static InterpolatorAffineTerm termToAffine(Term term) {
		if (term instanceof AnnotatedTerm) {
			term = ((AnnotatedTerm) term).getSubterm();
		}
		final SMTAffineTerm affine = new SMTAffineTerm(term);
		return new InterpolatorAffineTerm(affine);
	}

	/**
	 * Compute the interpolants for a Nelson-Oppen equality clause. This is a theory lemma of the form equality implies
	 * equality, where one equality is congruence closure and one is linear arithmetic.
	 *
	 * @param ccEq
	 *            the congruence closure equality atom
	 * @param laEq
	 *            the linear arithmetic equality atom
	 * @param sign
	 *            the sign of l1 in the conflict clause. This is -1 if l1 implies l2, and +1 if l2 implies l1.
	 */
	public Term[] computeInterpolants(final Term eqLemma) {
		Term[] interpolants = null;

		final InterpolatorClauseTermInfo lemmaTermInfo = mInterpolator.getClauseTermInfo(eqLemma);
		final Term ccEq = mInterpolator.getAtom(lemmaTermInfo.getCCEq());
		final Term laEq = mInterpolator.getAtom(lemmaTermInfo.getLAEq());
		final InterpolatorAtomInfo ccTermInfo = mInterpolator.getAtomTermInfo(ccEq);
		final InterpolatorAtomInfo laTermInfo = mInterpolator.getAtomTermInfo(laEq);
		final boolean ccIsNeg = mInterpolator.isNegatedTerm(lemmaTermInfo.getCCEq());

		final LitInfo ccOccInfo = mInterpolator.getAtomOccurenceInfo(ccEq);
		final LitInfo laOccInfo = mInterpolator.getAtomOccurenceInfo(laEq);

		interpolants = new Term[mInterpolator.mNumInterpolants];
		for (int p = 0; p < mInterpolator.mNumInterpolants; p++) {
			Term interpolant;
			if (ccOccInfo.isAorShared(p) && laOccInfo.isAorShared(p)) {
				interpolant = mInterpolator.mTheory.mFalse; // both literals in A.
			} else if (ccOccInfo.isBorShared(p) && laOccInfo.isBorShared(p)) {
				interpolant = mInterpolator.mTheory.mTrue; // both literals in B.
			} else {
				final InterpolatorAffineTerm iat = new InterpolatorAffineTerm();
				final Rational factor = lemmaTermInfo.getLAFactor();
				TermVariable mixed = null;
				boolean negate = false;
				// Get A part of ccEq:
				final ApplicationTerm ccEqApp = ccTermInfo.getEquality();
				if (ccOccInfo.isALocal(p)) {
					iat.add(factor, termToAffine(ccEqApp.getParameters()[0]));
					iat.add(factor.negate(), termToAffine(ccEqApp.getParameters()[1]));
					if (!ccIsNeg) {
						negate = true;
					}
				} else if (ccOccInfo.isMixed(p)) {
					// mixed;
					if (!ccIsNeg) {
						mixed = ccOccInfo.getMixedVar();
					}
					if (ccOccInfo.mLhsOccur.isALocal(p)) {
						iat.add(factor, termToAffine(ccEqApp.getParameters()[0]));
						iat.add(factor.negate(), ccOccInfo.getMixedVar());
					} else {
						iat.add(factor, ccOccInfo.getMixedVar());
						iat.add(factor.negate(), termToAffine(ccEqApp.getParameters()[1]));
					}
				} else {
					// both sides in B, A part is empty
				}

				// Get A part of laEq:
				if (laOccInfo.isALocal(p)) {
					iat.add(Rational.MONE, laTermInfo.getAffineTerm());
					if (ccIsNeg) {
						negate = true;
					}
				} else if (laOccInfo.isMixed(p)) {
					if (ccIsNeg) {
						mixed = laOccInfo.getMixedVar();
					}
					iat.add(Rational.MONE, laOccInfo.getAPart(p));
					iat.add(Rational.ONE, laOccInfo.getMixedVar());
				} else {
					// both sides in B, A part is empty
				}
				iat.mul(iat.getGcd().inverse());

				// Now solve it.
				if (mixed != null) { // NOPMD
					final Rational mixedFactor = iat.getSummands().remove(mixed);
					assert mixedFactor.isIntegral();
					final boolean isInt = mixed.getSort().getName().equals("Int");
					if (isInt && mixedFactor.abs() != Rational.ONE) { // NOPMD
						if (mixedFactor.signum() > 0) {
							iat.negate();
						}
						final Term sharedTerm = iat.toSMTLib(mInterpolator.mTheory, isInt);
						final Term divisor = mixedFactor.abs().toTerm(mixed.getSort());
						// We need to divide sharedTerm by mixedFactor and check that it doesn't produce a remainder.
						//
						// Interpolant is: (and (= mixed (div sharedTerm mixedFactor))
						// (= (mod sharedTerm mixedFactor) 0))
						interpolant = mInterpolator.mTheory.and(
								mInterpolator.mTheory.term(Interpolator.EQ, mixed,
										mInterpolator.mTheory.term("div", sharedTerm, divisor)),
								mInterpolator.mTheory.term("=", mInterpolator.mTheory.term("mod", sharedTerm, divisor),
										Rational.ZERO.toTerm(mixed.getSort())));
					} else {
						iat.mul(mixedFactor.negate().inverse());
						final Term sharedTerm = iat.toSMTLib(mInterpolator.mTheory, isInt);
						interpolant = mInterpolator.mTheory.term(Interpolator.EQ, mixed, sharedTerm);
					}
				} else {
					if (iat.isConstant()) {
						if (iat.getConstant() != InfinitesimalNumber.ZERO) {
							negate ^= true;
						}
						interpolant = negate ? mInterpolator.mTheory.mFalse : mInterpolator.mTheory.mTrue;
					} else {
						final boolean isInt = iat.isInt();
						final Sort sort = mInterpolator.mTheory.getSort(isInt ? "Int" : "Real");
						final Term term = iat.toSMTLib(mInterpolator.mTheory, isInt);
						final Term zero = Rational.ZERO.toTerm(sort);
						interpolant = negate ? mInterpolator.mTheory.not(mInterpolator.mTheory.equals(term, zero))
								: mInterpolator.mTheory.equals(term, zero);
					}
				}
			}
			interpolants[p] = interpolant;
		}
		return interpolants;
	}
}
