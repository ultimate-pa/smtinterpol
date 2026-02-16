/*
 * Copyright (C) 2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.EQUALS;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.GEQ;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.GT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.INT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.LEQ;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.LT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.MINUS;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.MUL;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.PLUS;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.TO_REAL;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;

/**
 * Proof rules for arithmetic.
 */
public class ArithmeticRules {

	public static Term expandMinus(FunctionSymbol f, Term[] params) {
		assert f.getName() == MINUS && params.length <= 2;
		assert params.length == 1 || params[0].getSort() == params[1].getSort();
		final Theory t = params[0].getTheory();
		final Term mone = Rational.MONE.toTerm(params[0].getSort());
		return params.length == 1 ? t.term(MUL, mone, params[0])
				: t.term(PLUS, params[0], t.term(MUL, mone, params[1]));
	}

	public static Term expandGt(FunctionSymbol f, Term[] params) {
		assert f.getName() == GT && params.length == 2;
		final Theory t = params[0].getTheory();
		return t.term(LT, params[1], params[0]);
	}

	public static Term expandGeq(FunctionSymbol f, Term[] params) {
		assert f.getName() == GEQ && params.length == 2;
		final Theory t = params[0].getTheory();
		return t.term(LEQ, params[1], params[0]);
	}

	public static ProofLiteral[] trichotomy(MinimalProofChecker checker, Theory theory, Term[] params) {
		return new ProofLiteral[] { new ProofLiteral(theory.term(LT, params), true),
				new ProofLiteral(theory.term(EQUALS, params), true),
				new ProofLiteral(theory.term(LT, params[1], params[0]), true) };
	}

	public static ProofLiteral[] total(MinimalProofChecker checker, Theory theory, Term[] params) {
		return new ProofLiteral[] { new ProofLiteral(theory.term(LEQ, params[0], params[1]), true),
				new ProofLiteral(theory.term(LT, params[1], params[0]), true) };

	}

	public static ProofLiteral[] totalInt(MinimalProofChecker checker, Theory theory, Term[] params) {
		final Term x = params[0];
		final Term cTerm = params[1];
		final Rational c = (Rational) ((ConstantTerm) cTerm).getValue();
		if (x.getSort().getName() != INT || cTerm.getSort() != x.getSort()
				|| !c.denominator().equals(BigInteger.ONE)) {
			return null;
		}
		final Term cPlusOne = c.add(Rational.ONE).toTerm(x.getSort());
		return new ProofLiteral[] { new ProofLiteral(theory.term(LEQ, x, cTerm), true),
				new ProofLiteral(theory.term(LEQ, cPlusOne, x), true) };
	}

	public static void registerRules(MinimalProofChecker checker) {
		checker.registerExpand(MINUS, ArithmeticRules::expandMinus);
		checker.registerExpand(GT, ArithmeticRules::expandGt);
		checker.registerExpand(GEQ, ArithmeticRules::expandGeq);
	}

	public static boolean checkFarkas(final Object[] params) {
		if (params.length % 2 != 0 || params.length < 2) {
			return false;
		}
		final Polynomial sum = new Polynomial();
		boolean strict = false;
		for (int i = 0; i < params.length; i+=2) {
			final BigInteger coeff = (BigInteger) params[i];
			final Term ineq = (Term) params[i + 1];
			if (coeff.signum() != 1) {
				return false;
			}
			if (ProofRules.isApplication(LT, ineq)) {
				strict = true;
			} else if (!ProofRules.isApplication(LEQ, ineq) && !ProofRules.isApplication(EQUALS, ineq)) {
				return false;
			}
			final ApplicationTerm appTerm = (ApplicationTerm) ineq;
			final Term[] polys = appTerm.getParameters();
			if (polys.length != 2) {
				return false;
			}
			final Rational coeffRat = Rational.valueOf(coeff, BigInteger.ONE);
			sum.add(coeffRat, polys[0]);
			sum.add(coeffRat.negate(), polys[1]);
		}
		final boolean okay = sum.isConstant() && sum.getConstant().signum() >= (strict ? 0 : 1);
		return okay;
	}

	public static boolean checkMulPos(final Term[] inequalities) {
		final Polynomial prod = new Polynomial();
		prod.add(Rational.ONE);
		boolean holdsStrictly = true;
		for (int i = 0; i < inequalities.length; i++) {
			if (ProofRules.isApplication(LEQ, inequalities[i])) {
				holdsStrictly = false;
			} else if (!ProofRules.isApplication(LT, inequalities[i])) {
				return false;
			}
			final ApplicationTerm appTerm = (ApplicationTerm) inequalities[i];
			final Term[] params = appTerm.getParameters();
			if (params.length != 2) {
				return false;
			}
			if (params[0] != Rational.ZERO.toTerm(params[0].getSort())) {
				return false;
			}
			if (i < inequalities.length - 1) {
				prod.mul(new Polynomial(params[1]));
			} else {
				if (!holdsStrictly && !ProofRules.isApplication(LEQ, inequalities[i])) {
					return false;
				}
				prod.add(Rational.MONE, params[1]);
			}
		}
		return prod.isZero();
	}

	private static Term computeFactorToReal(final Term factor) {
		if (factor instanceof ConstantTerm && ((ConstantTerm) factor).getValue() instanceof Rational) {
			return ((Rational) ((ConstantTerm) factor).getValue()).toTerm(factor.getTheory().getSort("Real"));
		} else {
			return factor.getTheory().term(TO_REAL, factor);
		}
	}

	private static Term computeMonomialToReal(final Term monomial) {
		if (ProofRules.isApplication(MUL, monomial)) {
			final Term[] oldParams = ((ApplicationTerm) monomial).getParameters();
			final Term[] newParams = new Term[oldParams.length];
			for (int i = 0; i < oldParams.length; i++) {
				newParams[i] = ArithmeticRules.computeFactorToReal(oldParams[i]);
			}
			return monomial.getTheory().term(MUL, newParams);
		} else {
			return ArithmeticRules.computeFactorToReal(monomial);
		}
	}

	public static Term computePolyToReal(final Term poly) {
		if (ProofRules.isApplication(PLUS, poly)) {
			final Term[] oldParams = ((ApplicationTerm) poly).getParameters();
			final Term[] newParams = new Term[oldParams.length];
			for (int i = 0; i < oldParams.length; i++) {
				newParams[i] = ArithmeticRules.computeMonomialToReal(oldParams[i]);
			}
			return poly.getTheory().term(PLUS, newParams);
		} else {
			return ArithmeticRules.computeMonomialToReal(poly);
		}
	}

	/**
	 * Check the parameters of a poly* axiom. It checks that the mulTerm is an
	 * application of `*` and that the product of its arguments minus the results
	 * (using polynomial multiplication and subtraction) gives zero.
	 *
	 * @param mulTerm
	 *            the mul term (first argument of the poly* axiom).
	 * @param result
	 *            the result term (second argument of the poly* axiom).
	 * @return true iff the parameters are wellformed.
	 */
	public static boolean checkPolyMul(final Term mulTerm, final Term result) {
		if (!ProofRules.isApplication(MUL, mulTerm)) {
			return false;
		}
		final Polynomial poly = new Polynomial();
		poly.add(Rational.ONE);
		for (final Term t : ((ApplicationTerm) mulTerm).getParameters()) {
			poly.mul(new Polynomial(t));
		}
		poly.add(Rational.MONE, result);
		if (!poly.isZero()) {
			System.err.println("STOP");
		}
		return poly.isZero();
	}

	/**
	 * Check the parameters of a poly+ axiom. It checks that the plusTerm is an
	 * application of `+` and that the sum of its arguments minus the results (using
	 * polynomial addition) sums to zero.
	 *
	 * @param plusTerm
	 *            the plus term (first argument of the poly+ axiom).
	 * @param result
	 *            the result term (second argument of the poly+ axiom).
	 * @return true iff the parameters are wellformed.
	 */
	public static boolean checkPolyAdd(final Term plusTerm, final Term result) {
		if (!ProofRules.isApplication(PLUS, plusTerm)) {
			return false;
		}
		final Polynomial poly = new Polynomial();
		for (final Term t : ((ApplicationTerm) plusTerm).getParameters()) {
			poly.add(Rational.ONE, t);
		}
		poly.add(Rational.MONE, result);
		return poly.isZero();
	}

}
