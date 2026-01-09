package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.math.BigInteger;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
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
	 * Checks if a term is an application of an internal function symbol.
	 *
	 * @param funcSym the expected function symbol.
	 * @param term    the term to check.
	 * @return true if term is an application of funcSym.
	 */
	public boolean isApplication(final String funcSym, final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol func = appTerm.getFunction();
			if (func.isIntern() && func.getName().equals(funcSym)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Prove that {@code (= constantTerm canonicalTerm)} where canonicalTerm is a
	 * rational constant, and constantTerm a constant rational term, e.g. a decimal
	 * or a numeral that is not in canonical form.
	 *
	 * @param constantTerm  the constant term
	 * @param canonicalTerm the rational term in canonical form.
	 * @return the proof for the equality.
	 */
	public Term proveConstEquality(final Term constantTerm, final Term canonicalTerm) {
		return proveTrivialEquality(constantTerm, canonicalTerm);
	}

	/**
	 * Prove that {@code (= (- term) canonicalTerm)} where canonicalTerm is a term
	 * in canonical form. On the left hand side, {@code term} should also be in
	 * canonical form .
	 *
	 * @param minusTerm     the unary minus term
	 * @param canonicalTerm the resulting term in canonical form.
	 * @return the proof for the equality.
	 */
	public Term proveUMinusEquality(final Term minusTerm, final Term canonicalTerm) {
		final Theory theory = minusTerm.getTheory();
		assert ((ApplicationTerm) minusTerm).getParameters().length == 1;
		final Term minusToPlus = ProofRules.computePolyMinus(minusTerm);
		if (minusToPlus == canonicalTerm) {
			// this can happen for positive constants.
			return mProofRules.minusDef(minusTerm);
		}
		final Term proof = res(theory.term(SMTLIBConstants.EQUALS, minusTerm, minusToPlus), mProofRules.minusDef(minusTerm),
				mProofRules.trans(minusTerm, minusToPlus, canonicalTerm));
		return res(theory.term(SMTLIBConstants.EQUALS, minusToPlus, canonicalTerm), mProofRules.polyMul(minusToPlus, canonicalTerm),
				proof);
	}

	/**
	 * Prove that {@code (= (- term term ...) canonicalTerm)} where canonicalTerm is
	 * a term in canonical form. On the left hand side, {@code term} should also be
	 * in canonical form .
	 *
	 * @param minusTerm     the non-unary minus term
	 * @param canonicalTerm the resulting term in canonical form.
	 * @return the proof for the equality.
	 */
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
	 * Prove that divTerm equals divResult. This works for `div` terms on constants
	 * as well as div on +/- 1 and some special div terms like `(div (+ (* 2 x) 1)
	 * 2)`.
	 *
	 * The condition is that `divTerm` is a term `(div x c)` with non-zero constant
	 * divisor and `(- (* (/ 1 c) x) divResult)` must be a rational constant between
	 * 0 (inclusive) and 1 (exclusive).
	 *
	 * @param divTerm   The div term.
	 * @param divResult The simplified result.
	 * @return the proof for `(= divTerm divResult)`.
	 */
	public Term proveDivEquality(final Term divTerm, final Term divResult) {
		final Theory theory = divTerm.getTheory();
		final Sort sort = divTerm.getSort();

		assert isApplication("div", divTerm);
		final Term[] divArgs = ((ApplicationTerm) divTerm).getParameters();
		assert divArgs.length == 2;
		final Rational divisor = Polynomial.parseConstant(divArgs[1]);
		assert divisor != null && divisor.isIntegral();

		// check that divResult is really syntactically the result of the division.
		// For (div x c) we compute (1/c * x - divResult), check that it is a constant
		// whose absolute value is less than one and that has the same sign as c.
		final Polynomial poly = new Polynomial();
		poly.add(Rational.MONE, divResult);
		poly.add(divisor.inverse(), divArgs[0]);
		assert poly.isConstant();
		final Rational remainder = poly.getConstant();
		assert remainder.abs().compareTo(Rational.ONE) < 0;
		assert remainder.signum() * divisor.signum() != -1;

		final Term zero = Rational.ZERO.toTerm(sort);
		final Term absDivArg = theory.term(SMTLIBConstants.ABS, divArgs[1]);
		final Term absDivisor = divisor.abs().toTerm(sort);
		final Term origDivLow = theory.term(SMTLIBConstants.LEQ, theory.term(SMTLIBConstants.MUL, divArgs[1], divTerm),
				divArgs[0]);
		final Term origDivHigh = theory.term(SMTLIBConstants.LT, divArgs[0],
				theory.term(SMTLIBConstants.PLUS, theory.term(SMTLIBConstants.MUL, divArgs[1], divTerm), absDivArg));
		final Polynomial diffAffine = new Polynomial(divTerm);
		diffAffine.add(Rational.MONE, divResult);
		final Term diffLhsRhs = diffAffine.toTerm(sort);
		Term proof = mProofRules.trichotomy(divTerm, divResult);
		Term ltLhsRhs = theory.term(SMTLIBConstants.LT, divTerm, divResult);
		Term gtLhsRhs = theory.term(SMTLIBConstants.LT, divResult, divTerm);
		final BigInteger[] oneone = new BigInteger[] { BigInteger.ONE, BigInteger.ONE };
		if (divisor.signum() < 0 || remainder.signum() != 0) {
			// we need total-int in the proof
			final Term leqLhsRhs = theory.term(SMTLIBConstants.LEQ, diffLhsRhs, zero);
			final Term geqLhsRhsOne = theory.term(SMTLIBConstants.LEQ, Rational.ONE.toTerm(sort), diffLhsRhs);
			proof = res(gtLhsRhs, proof, mProofRules.farkas(new Term[] { gtLhsRhs, leqLhsRhs }, oneone));
			proof = res(leqLhsRhs, mProofRules.totalInt(diffLhsRhs, BigInteger.ZERO), proof);
			gtLhsRhs = geqLhsRhsOne;
		}
		if (divisor.signum() > 0 || remainder.signum() != 0) {
			// we need total-int in the proof
			final Term geqLhsRhs = theory.term(SMTLIBConstants.LEQ, zero, diffLhsRhs);
			final Term leqLhsRhsOne = theory.term(SMTLIBConstants.LEQ, diffLhsRhs, Rational.MONE.toTerm(sort));
			proof = res(ltLhsRhs, proof, mProofRules.farkas(new Term[] { ltLhsRhs, geqLhsRhs }, oneone));
			proof = res(geqLhsRhs, mProofRules.totalInt(diffLhsRhs, BigInteger.ONE.negate()), proof);
			ltLhsRhs = leqLhsRhsOne;
		}
		final Term lhsRhsLow = divisor.signum() > 0 ? gtLhsRhs : ltLhsRhs;
		final Term lhsRhsHigh = divisor.signum() > 0 ? ltLhsRhs : gtLhsRhs;
		final BigInteger[] coeffs = new BigInteger[] { BigInteger.ONE, divisor.abs().numerator() };
		final BigInteger[] coeffs3 = new BigInteger[] { BigInteger.ONE, divisor.abs().numerator(), BigInteger.ONE };
		final Term eqAbs = theory.term(SMTLIBConstants.EQUALS, absDivArg, absDivisor);
		proof = res(lhsRhsLow, proof, mProofRules.farkas(new Term[] { origDivLow, lhsRhsLow }, coeffs));
		proof = res(lhsRhsHigh, proof, mProofRules.farkas(new Term[] { origDivHigh, lhsRhsHigh, eqAbs }, coeffs3));
		proof = res(eqAbs, proveAbsConstant(divisor, sort), proof);
		proof = res(origDivHigh, mProofRules.divHigh(divArgs[0], divArgs[1]), proof);
		proof = res(origDivLow, mProofRules.divLow(divArgs[0], divArgs[1]), proof);
		return proof;
	}

	/**
	 * Prove that modTerm equals modResult. This works for `mod` terms on constants
	 * as well as div on +/- 1 and some special mod terms like `(mod (+ (* 2 x) 1)
	 * 2)`.
	 *
	 * The condition is that `modTerm` is a term `(mod x c)` with non-zero constant
	 * divisor, `modResult` is an integer constant between 0 and |c|,
	 * and `(* (/ 1 c) (- x modResult))` must have only integer coefficients.
	 *
	 * @param modTerm   The mod term.
	 * @param modResult The simplified result.
	 * @return the proof for `(= divTerm divResult)`.
	 */
	public Term proveModConstant(final Term modTerm, final Term modResult) {
		final Theory theory = modTerm.getTheory();
		final Sort sort = modTerm.getSort();

		assert isApplication("mod", modTerm);
		final Term[] divArgs = ((ApplicationTerm) modTerm).getParameters();
		assert divArgs.length == 2;
		final Rational divisor = Polynomial.parseConstant(divArgs[1]);
		assert divisor != null && divisor.isIntegral();

		final Polynomial poly = new Polynomial();
		poly.add(divisor.inverse(), divArgs[0]);
		final Rational modulo = Polynomial.parseConstant(modResult);
		assert modulo.signum() >= 0;
		assert modulo.abs().compareTo(divisor) < 0;
		poly.add(modulo.div(divisor).negate());

		assert poly.getGcd().isIntegral();
		final Term divResult = poly.toTerm(sort);
		final Term divTerm = theory.term(SMTLIBConstants.DIV, divArgs);

		final Term divEqProof = proveDivEquality(divTerm, divResult);
		final Term divModEqProof = mProofRules.modDef(divArgs[0], divArgs[1]);
		final Term divEq = theory.term(SMTLIBConstants.EQUALS, divTerm, divResult);
		final Term divModEq = theory.term(SMTLIBConstants.EQUALS,
				theory.term(SMTLIBConstants.PLUS,
						theory.term(SMTLIBConstants.MUL, divArgs[1], divTerm), modTerm),
				divArgs[0]);
		final Term modEq = theory.term(SMTLIBConstants.EQUALS, modTerm, modResult);

		return res(divEq, divEqProof,
				res(divModEq, divModEqProof, proveEqualityFromEqualities(new Term[] { modEq, divEq, divModEq },
						new BigInteger[] { BigInteger.ONE, divisor.numerator(), BigInteger.ONE.negate() })));
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

	/**
	 * Proof a linear equality eqs[0] from other equalities eqs[1],...eq[n].
	 * The coeffs must be chosen such that sum coeffs[i]*eq[i] evaluates to a trivial equality,
	 * with both sides being equal.
	 * @param eqs The equality terms that are combined. eqs[0] is the equality that is proved.
	 * @param coeffs The farkas coefficients; they can be negative.
	 * @return the proof for eqs[0] from eqs[1],...,eqs[n].
	 */
	public Term proveEqualityFromEqualities(final Term[] eqs, final BigInteger[] coeffs) {
		final Theory theory = eqs[0].getTheory();
		assert eqs.length == coeffs.length;
		final BigInteger[] absCoeffs = new BigInteger[coeffs.length];
		final Term[] farkas1 = new Term[coeffs.length];
		final Term[] farkas2 = new Term[coeffs.length];
		for (int i = 0; i < coeffs.length; i++) {
			absCoeffs[i] = coeffs[i].abs();
			final Term[] eqArgs = ((ApplicationTerm) eqs[i]).getParameters();
			final Term t1 = i == 0 ? theory.term(SMTLIBConstants.LT, eqArgs[0], eqArgs[1]) : eqs[i];
			final Term t2 = theory.term(i == 0 ? SMTLIBConstants.LT : SMTLIBConstants.EQUALS, eqArgs[1], eqArgs[0]);
			farkas1[i] = coeffs[i].signum() > 0 ? t1 : t2;
			farkas2[i] = coeffs[i].signum() > 0 ? t2 : t1;
		}
		final Term[] eq0Args = ((ApplicationTerm) eqs[0]).getParameters();
		Term proof = res(farkas1[0], res(farkas2[0], mProofRules.trichotomy(eq0Args[0], eq0Args[1]),
				mProofRules.farkas(farkas2, absCoeffs)), mProofRules.farkas(farkas1, absCoeffs));
		for (int i = 1; i < coeffs.length; i++) {
			final Term[] eqArgs = ((ApplicationTerm) eqs[i]).getParameters();
			final Term eqSwapped = theory.term(SMTLIBConstants.EQUALS, eqArgs[1], eqArgs[0]);
			proof = res(eqSwapped, mProofRules.symm(eqArgs[1], eqArgs[0]), proof);
		}
		return proof;
	}

	/**
	 * Proof a linear equality rhs from a linear equality lhs. This proves
	 *
	 * <pre>
	 * (=&gt; (= lhs[0] lhs[1]) (= rhs[0] rhs[1])
	 * </pre>
	 *
	 * where (lhs[0] - lhs[1]) * multiplier == (rhs[0] - rhs[1]).
	 *
	 * @param lhs        the terms that are known to be equal
	 * @param rhs        the terms that should be proved to be equal.
	 * @param multiplier the factor that makes the sides equal.
	 * @return the proof.
	 */
	public Term proveEqWithMultiplier(final Term[] lhs, final Term[] rhs, final Rational multiplier) {
		final Theory theory = lhs[0].getTheory();
		return proveEqualityFromEqualities(
				new Term[] { theory.term(SMTLIBConstants.EQUALS, rhs[0], rhs[1]),
						theory.term(SMTLIBConstants.EQUALS, lhs[0], lhs[1]) },
				new BigInteger[] { multiplier.denominator(), multiplier.numerator().negate() });
	}

	/**
	 * Prove that {@code (= (/ term constant) canonicalTerm)} where canonicalTerm is
	 * a term in canonical form. On the left hand side, {@code term} should also be
	 * in canonical form .
	 *
	 * @param divideTerm    the divide term
	 * @param canonicalTerm the resulting term in canonical form.
	 * @return the proof for the equality.
	 */
	public Term proveDivideEquality(Term divideTerm, Term canonicalTerm) {
		assert isApplication(SMTLIBConstants.DIVIDE, divideTerm);
		final Theory theory = divideTerm.getTheory();
		final Term[] divideArgs = ((ApplicationTerm) divideTerm).getParameters();
		Term proofDivDef = mProofRules.divideDef(divideTerm);
		final Sort sort = divideTerm.getSort();
		final Term zero = Rational.ZERO.toTerm(sort);
		final Term[] mulTermArgs = new Term[divideArgs.length];
		Rational multiplier = Rational.ONE;
		for (int i = 1; i < divideArgs.length; i++) {
			final Term eqZero = theory.term(SMTLIBConstants.EQUALS, divideArgs[i], zero);
			proofDivDef = res(eqZero, proofDivDef, proveTrivialDisequality(divideArgs[i], zero));
			multiplier = multiplier.mul(Polynomial.parseConstant(divideArgs[i]));
			mulTermArgs[i - 1] = divideArgs[i];
		}
		mulTermArgs[mulTermArgs.length - 1] = divideTerm;
		Term mulTerm = theory.term("*", mulTermArgs);
		if (mulTermArgs.length > 2) {
			final Term mulShortTerm = theory.term("*", multiplier.toTerm(sort), divideTerm);
			proofDivDef = res(theory.term(SMTLIBConstants.EQUALS, mulShortTerm, mulTerm),
					res(theory.term(SMTLIBConstants.EQUALS, mulTerm, mulShortTerm),
							mProofRules.polyMul(mulTerm, mulShortTerm), mProofRules.symm(mulShortTerm, mulTerm)),
					mProofRules.trans(mulShortTerm, mulTerm, divideArgs[0]));
			mulTerm = mulShortTerm;
		}
		// now mulTerm is (* multiplier lhs)
		// and proofDivDef is a proof for (= mulTerm lhsArgs[0])
		return res(theory.term(SMTLIBConstants.EQUALS, mulTerm, divideArgs[0]), proofDivDef, proveEqWithMultiplier(
				new Term[] { mulTerm, divideArgs[0] }, new Term[] { divideTerm, canonicalTerm }, multiplier.inverse()));
	}

	/**
	 * Prove the disequality between two distinct bitvector constant terms.
	 *
	 * @param bv1 the left-hand side of the equality
	 * @param bv2 the right-hand side of the equality
	 * @return the proof for `~(= bv1 bv2)` or null if this is not a trivial
	 *         disequality.
	 */
	public Term proveBitVecDisequality(final Term bv1, final Term bv2) {
		final Theory theory = bv1.getTheory();
		final BigInteger val1 = (BigInteger) ((ConstantTerm) bv1).getValue();
		final BigInteger val2 = (BigInteger) ((ConstantTerm) bv2).getValue();
		final Sort intSort = theory.getSort(SMTLIBConstants.INT);
		final Term nat1 = Rational.valueOf(val1, BigInteger.ONE).toTerm(intSort);
		final Term nat2 = Rational.valueOf(val2, BigInteger.ONE).toTerm(intSort);
		final Term bvnat1 = theory.term(SMTLIBConstants.INT_TO_BV, nat1);
		final Term bvnat2 = theory.term(SMTLIBConstants.INT_TO_BV, nat2);
		final Term intbvnat1 = theory.term(SMTLIBConstants.UBV_TO_INT, nat1);
		final Term intbvnat2 = theory.term(SMTLIBConstants.UBV_TO_INT, nat2);
		final BigInteger bitLength = new BigInteger(bv1.getSort().getIndices()[0]);
		final BigInteger pow2 = BigInteger.ONE.shiftLeft(Integer.parseInt(bv1.getSort().getIndices()[0]));
		final Term pow2Term = Rational.valueOf(pow2, BigInteger.ONE).toTerm(intSort);
		final Term modNat1 = theory.term(SMTLIBConstants.MOD, nat1, pow2Term);
		final Term modNat2 = theory.term(SMTLIBConstants.MOD, nat2, pow2Term);


		final Term bv1EqBvNat1 = mProofRules.bvConst(val1, bitLength);
		final Term bv2EqBvNat2 = mProofRules.bvConst(val2, bitLength);


		/*
		mProofRules.int2ubv2int(bitLength, nat1);
		mProofRules.trans(modNat1, intbvnat1, intbvnat2, modNat2);
		mProofRules.trans(bvnat1, bv1, bv2, bvnat2);
		mProofRules.symm(bvnat1, bv1);
		mProofRules.symm(modNat1, intbvnat1);
		mProofRules.int2ubv2int(bitLength, nat1);
		mProofRules.int2ubv2int(bitLength, nat2);
		mProofRules.modDef(nat1, pow2Term);
		mProofRules.modDef(nat2, pow2Term);
		proveTrivialDisequality(bv1EqBvNat1, bv2EqBvNat2);
		*/

		return mProofRules.oracle(
				new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, bv1, bv2), false) },
				new Annotation[] { new Annotation(":bvdiseq", null) });
	}

	/**
	 * Prove the disequality between two distinct constant datatype terms.
	 *
	 * @param dt1 the left-hand side of the equality
	 * @param dt2 the right-hand side of the equality
	 * @return the proof for `~(= dt1 dt2)`.
	 */
	public Term proveDTDisequality(final Term dt1, final Term dt2) {
		final Theory theory = dt1.getTheory();
		final ApplicationTerm dt1app = (ApplicationTerm) dt1;
		final ApplicationTerm dt2app = (ApplicationTerm) dt2;
		final DataType dt = (DataType) dt1.getSort().getSortSymbol();
		assert dt1 != dt2;
		assert dt1app.getFunction().isConstructor();
		assert dt2app.getFunction().isConstructor();
		final String consName1 = dt1app.getFunction().getName();
		if (dt1app.getFunction() != dt2app.getFunction()) {
			final FunctionSymbol tester =
					theory.getFunctionWithResult(SMTLIBConstants.IS, new String[] { consName1 }, null, dt1.getSort());
			final Term tester1 = theory.term(tester, dt1app);
			final Term tester2 = theory.term(tester, dt2app);
			final Term eqTesters = theory.term(SMTLIBConstants.EQUALS, tester1, tester2);
			return res(eqTesters,
				mProofRules.cong(tester1, tester2),
				res(tester1, mProofRules.dtTestI(dt1app),
						res(tester2, mProofRules.iffElim2(eqTesters),
									mProofRules.dtTestE(consName1, dt2app))));
		} else {
			final Term[] dt1args = dt1app.getParameters();
			final Term[] dt2args = dt2app.getParameters();
			for (int i = 0; i < dt1args.length; i++) {
				if (dt1args[i] != dt2args[i]) {
					final Constructor cons = dt.getConstructor(consName1);
					final FunctionSymbol selector = theory.getFunction(cons.getSelectors()[i], dt1app.getSort());
					final Term seldt1 = theory.term(selector, dt1);
					final Term seldt2 = theory.term(selector, dt2);
					final Term subproof = proveDTDisequality(dt1args[i], dt2args[i]);
					Term proof = res(theory.term(SMTLIBConstants.EQUALS, seldt1, seldt2),
							mProofRules.cong(seldt1, seldt2),
							res(theory.term(SMTLIBConstants.EQUALS, dt1args[i], dt2args[i]),
									mProofRules.trans(dt1args[i], seldt1, seldt2, dt2args[i]),
									subproof));
					proof = res(theory.term(SMTLIBConstants.EQUALS, seldt2, dt2args[i]),
							mProofRules.dtProject(seldt2), proof);
					proof = res(theory.term(SMTLIBConstants.EQUALS, seldt1, dt1args[i]), mProofRules.dtProject(seldt1),
							res(theory.term(SMTLIBConstants.EQUALS, dt1args[i], seldt1),
									mProofRules.symm(dt1args[i], seldt1), proof));
					return proof;
				}
			}
			throw new AssertionError("different data types with same arguments");
		}
	}

	/**
	 * Prove a select over store of const for constant arguments.
	 *
	 * @param term  the `select(store(...store(const v, ...)..., i, vi), ik)` term.
	 * @param value the value to which the select term evaluates to.
	 * @return the proof for `(= term value)`.
	 */
	public Term proveSelectOverStore(final Term term, final Term value) {
		final Theory theory = term.getTheory();
		ApplicationTerm selectTerm = (ApplicationTerm) term;
		final FunctionSymbol selectFunc = selectTerm.getFunction();
		Term array = selectTerm.getParameters()[0];
		final Term index = selectTerm.getParameters()[1];
		Term proof = null;
		while (isApplication(SMTLIBConstants.STORE, array)) {
			final Term[] storeArgs = ((ApplicationTerm) array).getParameters();
			if (storeArgs[1] == index) {
				assert storeArgs[2] == value;
				proof = res(theory.term(SMTLIBConstants.EQUALS, selectTerm, value),
						mProofRules.selectStore1(storeArgs[0], storeArgs[1], storeArgs[2]), proof);
				return proof;
			}
			final Term subSelectTerm = theory.term(selectFunc, storeArgs[0], index);
			proof = res(theory.term(SMTLIBConstants.EQUALS, selectTerm, value),
					res(theory.term(SMTLIBConstants.EQUALS, storeArgs[1], index),
							res(theory.term(SMTLIBConstants.EQUALS, selectTerm, subSelectTerm),
									mProofRules.selectStore2(array, index, value, index),
							mProofRules.trans(selectTerm, subSelectTerm, value)),
							proveDisequality(storeArgs[1], index)),
					proof);

			array = storeArgs[0];
			selectTerm = (ApplicationTerm) theory.term(selectFunc, array, index);
		}
		assert isApplication(SMTLIBConstants.CONST, array);
		return res(theory.term(SMTLIBConstants.EQUALS, selectTerm, value), mProofRules.constArray(value, index), proof);
	}

	/**
	 * Return the value stored in the given constant array at the given constant
	 * index.
	 *
	 * @param array the constant array term (store of store of const)
	 * @param index the constant index term.
	 * @return the constant value stored in the array.
	 */
	private Term evaluateSelect(Term array, Term index) {
		while (isApplication(SMTLIBConstants.STORE, array)) {
			final Term[] storeArgs = ((ApplicationTerm) array).getParameters();
			if (storeArgs[1] == index) {
				return storeArgs[2];
			}
			array = storeArgs[0];
		}
		if (isApplication(SMTLIBConstants.CONST, array)) {
			return ((ApplicationTerm) array).getParameters()[0];
		}
		throw new AssertionError("Not a valid array constant");
	}

	/**
	 * Return a (constant) index term where the two constant arrays differ.
	 *
	 * @param array1 the first constant array term (store of store of const)
	 * @param array2 the second constant array term.
	 * @return the constant index term where they differ.
	 */
	private Term findDistinctIndices(Term array1, Term array2) {
		while (isApplication(SMTLIBConstants.STORE, array1)) {
			final Term[] storeArgs = ((ApplicationTerm) array1).getParameters();
			if (storeArgs[2] == evaluateSelect(array2, storeArgs[1])) {
				return storeArgs[1];
			}
			array1 = storeArgs[0];
		}
		while (isApplication(SMTLIBConstants.STORE, array2)) {
			final Term[] storeArgs = ((ApplicationTerm) array2).getParameters();
			if (storeArgs[2] == evaluateSelect(array1, storeArgs[1])) {
				return storeArgs[1];
			}
			array2 = storeArgs[0];
		}
		// two const arrays. They differ on any "fresh" index
		throw new AssertionError("Fresh Index not yet implemented");
	}

	/**
	 * Prove the disequality between two distinct constant array terms.
	 *
	 * @param arr1 the left-hand side of the equality
	 * @param arr2 the right-hand side of the equality
	 * @return the proof for `~(= arr1 arr2)`.
	 */
	public Term proveArrayDisequality(final Term arr1, final Term arr2) {
		// First we determine the index where arr1 and arr2 differ.
		final Theory theory = arr1.getTheory();
		final Term index = findDistinctIndices(arr1, arr2);
		final Term val1 = evaluateSelect(arr1, index);
		final Term val2 = evaluateSelect(arr2, index);
		assert val1 != val2;
		final Term sel1 = theory.term(SMTLIBConstants.SELECT, arr1, index);
		final Term sel2 = theory.term(SMTLIBConstants.SELECT, arr2, index);
		final Term val1Eq = proveSelectOverStore(sel1, val1);
		final Term val2Eq = proveSelectOverStore(sel2, val2);
		final Term eqSelect = theory.term(SMTLIBConstants.EQUALS, sel1, sel2);
		return res(eqSelect,
				res(theory.term(SMTLIBConstants.EQUALS, index, index),
						mProofRules.refl(index),
						mProofRules.cong(sel1, sel2)),
				res(theory.term(SMTLIBConstants.EQUALS, val1, val2),
						res(theory.term(SMTLIBConstants.EQUALS, sel2, val2), val2Eq,
								res(theory.term(SMTLIBConstants.EQUALS, val1, sel1),
										res(theory.term(SMTLIBConstants.EQUALS, sel1, val1), val1Eq,
												mProofRules.symm(val1, sel1)),
						mProofRules.trans(val1, sel1, sel2, val2))),
						proveDisequality(val1, val2)));
	}

	/**
	 * Prove the disequality between two distinct constant terms in normalized form.
	 *
	 * @param t1 the left-hand side of the equality
	 * @param t2 the right-hand side of the equality
	 * @return the proof for `~(= t1 t2)` or null if this is not a trivial
	 *         disequality.
	 */
	public Term proveDisequality(final Term t1, final Term t2) {
		final Sort sort = t1.getSort();
		if (sort.isNumericSort()) {
			return proveTrivialDisequality(t1, t2);
		} else if (sort.isBitVecSort()) {
			return proveBitVecDisequality(t1, t2);
		} else if (sort.isArraySort()) {
			return proveArrayDisequality(t1, t2);
		} else if (sort.getSortSymbol().isDatatype()) {
			return proveDTDisequality(t1, t2);
		} else {
			// TODO: Do we want model value disequalities? Or do we make them datatypes?
			final Theory theory = t1.getTheory();
			return mProofRules.oracle(
					new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, t1, t2), false) },
					new Annotation[] { new Annotation(":trivialdiseq", null) });
		}
	}
}
