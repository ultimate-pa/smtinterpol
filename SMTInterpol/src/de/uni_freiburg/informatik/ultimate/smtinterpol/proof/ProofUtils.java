package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.math.BigInteger;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;

public class ProofUtils {

	ProofRules mProofRules;

	public ProofUtils(ProofRules rules) {
		mProofRules = rules;
	}

	/**
	 * Resolution rule which handles null proofs (for not resolving).
	 *
	 * @param pivot    The pivot literal.
	 * @param proofPos The proof proving `+ pivot`.
	 * @param proofNeg The proof proving `- pivot`.
	 * @return the combined proof.
	 */
	public Term res(final Term pivot, final Term proofPos, final Term proofNeg) {
		return proofPos == null ? proofNeg
				: proofNeg == null ? proofPos : mProofRules.resolutionRule(pivot, proofPos, proofNeg);
	}

	/**
	 * Prove that `(= constantTerm canonicalTerm)` where canonicalTerm is a rational
	 * constant, and constantTerm a constant rational term, e.g. a decimal or a
	 * numeral that is not in canonical form.
	 *
	 * @param constantTerm  the constant term
	 * @param canonicalTerm the rational term in canonical form.
	 * @return the proof for the equality.
	 */
	public Term proveConstEquality(final Term constantTerm, final Term canonicalTerm) {
		return proveTrivialEquality(constantTerm, canonicalTerm);
	}

	public Term proveUMinusEquality(final Term minusTerm, final Term canonicalTerm) {
		final Theory theory = minusTerm.getTheory();
		assert ((ApplicationTerm) minusTerm).getParameters().length == 1;
		final Term minusToPlus = ProofRules.computePolyMinus(minusTerm);
		if (minusToPlus == canonicalTerm) {
			return mProofRules.minusDef(minusTerm);
		}
		final Term proof = res(theory.term(SMTLIBConstants.EQUALS, minusTerm, minusToPlus), mProofRules.minusDef(minusTerm),
				mProofRules.trans(minusTerm, minusToPlus, canonicalTerm));
		return res(theory.term(SMTLIBConstants.EQUALS, minusToPlus, canonicalTerm), mProofRules.polyMul(minusToPlus, canonicalTerm),
				proof);
	}

	public Term proveMinusEquality(final Term minusTerm, final Term canonicalTerm) {
		final Theory theory = minusTerm.getTheory();
		final Term minusToPlus = ProofRules.computePolyMinus(minusTerm);
		final Term[] lhsArgs = ((ApplicationTerm) minusTerm).getParameters();
		assert lhsArgs.length >= 2;
		final Term[] expectedArgs = new Term[lhsArgs.length];
		expectedArgs[0] = lhsArgs[0];
		for (int i = 1; i < lhsArgs.length; i++) {
			final Polynomial affineTerm = new Polynomial();
			affineTerm.add(Rational.MONE, lhsArgs[i]);
			expectedArgs[i] = affineTerm.toTerm(lhsArgs[i].getSort());
		}
		final Term expectedPlus = theory.term(SMTLIBConstants.PLUS, expectedArgs);
		Term proof;
		if (expectedPlus != canonicalTerm) {
			proof = res(theory.term(SMTLIBConstants.EQUALS, expectedPlus, canonicalTerm),
					mProofRules.polyAdd(expectedPlus, canonicalTerm),
					mProofRules.trans(minusTerm, minusToPlus, expectedPlus, canonicalTerm));
		} else {
			proof = mProofRules.trans(minusTerm, minusToPlus, expectedPlus);
		}
		proof = res(theory.term(SMTLIBConstants.EQUALS, minusTerm, minusToPlus), mProofRules.minusDef(minusTerm),
				proof);
		proof = res(theory.term(SMTLIBConstants.EQUALS, minusToPlus, expectedPlus),
				mProofRules.cong(minusToPlus, expectedPlus), proof);
		final HashSet<Term> seenEqs = new HashSet<>();
		final Term[] minusToPlusArgs = ((ApplicationTerm) minusToPlus).getParameters();
		for (int i = 0; i < minusToPlusArgs.length; i++) {
			final Term eq = theory.term(SMTLIBConstants.EQUALS, minusToPlusArgs[i], expectedArgs[i]);
			if (seenEqs.add(eq)) {
				final Term proofEq = minusToPlusArgs[i] == expectedArgs[i] ? mProofRules.refl(minusToPlusArgs[i])
						: mProofRules.polyMul(minusToPlusArgs[i], expectedArgs[i]);
				proof = res(eq, proofEq, proof);
			}
		}
		return proof;
	}

	/**
	 * Prove that `(= (abs rat) |rat|)` where rat is a rational constant, |rat| is
	 * the rational for the absolute value of rat, and `(abs rat)` is the SMTLIB
	 * function abs applied to rat.
	 *
	 * @param rat  the rational constant
	 * @param sort the sort of the constant.
	 * @return the proof for the equality.
	 */
	public Term proveAbsConstant(final Rational rat, final Sort sort) {
		final Theory theory = sort.getTheory();
		final Term x = rat.toTerm(sort);
		final Term absX = rat.abs().toTerm(sort);
		final Term zero = Rational.ZERO.toTerm(sort);
		final Term ltXZero = theory.term("<", x, zero);
		Term proof = proveAbsEquality(x, absX);
		if (x == absX) {
			proof = res(ltXZero, proof,
					mProofRules.farkas(new Term[] { ltXZero }, new BigInteger[] { BigInteger.ONE }));
		} else {
			proof = res(ltXZero, mProofRules.total(zero, x), proof);
			final Term leqZeroX = theory.term(SMTLIBConstants.LEQ, zero, x);
			proof = res(leqZeroX, proof,
					mProofRules.farkas(new Term[] { leqZeroX }, new BigInteger[] { BigInteger.ONE }));
		}
		return proof;
	}

	/**
	 * Prove {@code -(< t 0), +(= (abs t) (- t))} or
	 * {@code +(< t 0), +(= (abs t) t)}.
	 *
	 * @param t    The term whose abs is taken.
	 * @param absT The absolute term t, must be equal to t or (- t).
	 * @return the proof.
	 */
	public Term proveAbsEquality(final Term t, final Term absT) {
		final Theory theory = t.getTheory();
		final Term litAbsT = theory.term(SMTLIBConstants.ABS, t);
		final Term zero = Rational.ZERO.toTerm(t.getSort());
		final Term ltXZero = theory.term("<", t, zero);
		final Term absxDef = theory.term("ite", ltXZero, theory.term("-", t), t);
		Term proof;
		if (t != absT) {
			final Term minusT = theory.term("-", t);
			proof = minusT == absT ? mProofRules.trans(litAbsT, absxDef, minusT)
					: mProofRules.trans(litAbsT, absxDef, minusT, absT);
			proof = res(theory.term(SMTLIBConstants.EQUALS, absxDef, minusT), mProofRules.ite1(absxDef), proof);
			final Term eqMinusX = theory.term(SMTLIBConstants.EQUALS, minusT, absT);
			if (minusT != absT) {
				proof = res(eqMinusX, proveUMinusEquality(minusT, absT), proof);
			}
		} else {
			proof = mProofRules.trans(litAbsT, absxDef, t);
			proof = res(theory.term(SMTLIBConstants.EQUALS, absxDef, t), mProofRules.ite2(absxDef), proof);
		}
		proof = res(theory.term(SMTLIBConstants.EQUALS, litAbsT, absxDef), mProofRules.expand(litAbsT), proof);
		return proof;
	}

	/**
	 * Prove that first and second are equal (modulo order of operands for +).
	 *
	 * @param first  the left-hand side of the equality
	 * @param second the right-hand side of the equality
	 * @return the proof for `(= first second)`.
	 */
	public Term proveTrivialEquality(final Term first, final Term second) {
		if (first == second) {
			return mProofRules.refl(first);
		}
		final Theory theory = first.getTheory();
		final Term ltTerm = theory.term(SMTLIBConstants.LT, first, second);
		final Term gtTerm = theory.term(SMTLIBConstants.LT, second, first);
		final BigInteger[] one = new BigInteger[] { BigInteger.ONE };
		return res(ltTerm,
				res(gtTerm, mProofRules.trichotomy(first, second), mProofRules.farkas(new Term[] { gtTerm }, one)),
				mProofRules.farkas(new Term[] { ltTerm }, one));
	}

	/**
	 * Prove that the disequality between two terms is trivial. There are two cases,
	 * (1) the difference between the terms is constant and nonzero, e.g.
	 * {@code (= x (+ x 1))}, or (2) the difference contains only integer variables
	 * and the constant divided by the gcd of the factors is non-integral, e.g.,
	 * {@code (= (+ x (* 2 y)) (+ x (* 2 z) 1))}.
	 *
	 * @param first  the left-hand side of the equality
	 * @param second the right-hand side of the equality
	 * @return the proof for `~(= first second)` or null if this is not a trivial
	 *         disequality.
	 */
	public Term proveTrivialDisequality(final Term first, final Term second) {
		final Theory theory = first.getTheory();
		final Polynomial diff = new Polynomial(first);
		diff.add(Rational.MONE, second);
		if (diff.isConstant()) {
			if (diff.getConstant().signum() > 0) {
				final Term eqLhs = theory.term(SMTLIBConstants.EQUALS, first, second);
				return mProofRules.farkas(new Term[] { eqLhs }, new BigInteger[] { BigInteger.ONE });
			} else {
				assert (diff.getConstant().signum() < 0);
				final Term eqSwapped = theory.term(SMTLIBConstants.EQUALS, second, first);
				return mProofRules.resolutionRule(eqSwapped, mProofRules.symm(second, first),
						mProofRules.farkas(new Term[] { eqSwapped }, new BigInteger[] { BigInteger.ONE }));
			}
		} else {
			final Rational gcd = diff.getGcd();
			diff.mul(gcd.inverse());
			final Rational bound = diff.getConstant().negate();
			if (!diff.isAllIntSummands() || bound.isIntegral()) {
				return null;
			}
			final Sort intSort = theory.getSort(SMTLIBConstants.INT);
			diff.add(bound);
			final Term intVar = diff.toTerm(intSort);
			final Term floorBound = bound.floor().toTerm(intSort);
			final Term ceilBound = bound.ceil().toTerm(intSort);
			assert ceilBound != floorBound;
			// show (ceil(bound) <= intVar) || (intVar <= floor(bound)
			final Term geqCeil = theory.term(SMTLIBConstants.LEQ, ceilBound, intVar);
			final Term leqFloor = theory.term(SMTLIBConstants.LEQ, intVar, floorBound);
			final Term proofIntCase = mProofRules.totalInt(intVar, bound.floor().numerator());
			// show inequality in both cases
			final Term eqLhs = theory.term(SMTLIBConstants.EQUALS, first, second);
			final Term eqSwapped = theory.term(SMTLIBConstants.EQUALS, second, first);
			final Term caseCeil = mProofRules.farkas(new Term[] { eqLhs, geqCeil },
					new BigInteger[] { gcd.denominator(), gcd.numerator() });
			final Term caseFloor = mProofRules.resolutionRule(eqSwapped, mProofRules.symm(second, first),
					mProofRules.farkas(new Term[] { eqSwapped, leqFloor },
							new BigInteger[] { gcd.denominator(), gcd.numerator() }));
			return mProofRules.resolutionRule(leqFloor, mProofRules.resolutionRule(geqCeil, proofIntCase, caseCeil),
					caseFloor);
		}
	}

}
