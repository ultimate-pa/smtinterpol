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

import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.AND;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BITVEC;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVADD;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVAND;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVCOMP;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVMUL;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVNAND;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVNEG;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVNEGO;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVNOR;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVNOT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVOR;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVSADDO;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVSDIV;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVSDIVO;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVSGE;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVSGT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVSLE;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVSLT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVSMOD;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVSMULO;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVSREM;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVSSUBO;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVSUB;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVUADDO;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVUDIV;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVUGE;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVUGT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVULE;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVULT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVUMULO;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVUREM;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVUSUBO;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVXNOR;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVXOR;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.CONCAT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.DIV;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.EQUALS;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.EXTRACT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.INT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.INT_TO_BV;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.ITE;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.LEQ;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.LT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.MOD;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.MUL;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.OR;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.PLUS;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.REPEAT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.ROTATE_LEFT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.ROTATE_RIGHT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.SBV_TO_INT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.SIGN_EXTEND;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.UBV_TO_INT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.ZERO_EXTEND;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;

/**
 * Helper class to expand bitvector operations.
 */
public class BitvectorRules {

	public static void registerRules(MinimalProofChecker checker) {
		checker.registerExpand(BVADD, BitvectorRules::expandBvAdd);
		checker.registerExpand(BVSUB, BitvectorRules::expandBvSub);
		checker.registerExpand(BVNEG, BitvectorRules::expandBvNeg);
		checker.registerExpand(BVMUL, BitvectorRules::expandBvMul);
		checker.registerExpand(BVUDIV, BitvectorRules::expandBvUdiv);
		checker.registerExpand(BVUREM, BitvectorRules::expandBvUrem);
		checker.registerExpand(BVSDIV, BitvectorRules::expandBvSdiv);
		checker.registerExpand(BVSREM, BitvectorRules::expandBvSrem);
		checker.registerExpand(BVSMOD, BitvectorRules::expandBvSmod);
		checker.registerExpand(BVNEGO, BitvectorRules::expandBvNegO);
		checker.registerExpand(BVUADDO, BitvectorRules::expandBvUAddO);
		checker.registerExpand(BVSADDO, BitvectorRules::expandBvSAddO);
		checker.registerExpand(BVUMULO, BitvectorRules::expandBvUMulO);
		checker.registerExpand(BVSMULO, BitvectorRules::expandBvSMulO);
		checker.registerExpand(BVSDIVO, BitvectorRules::expandBvSDivO);
		checker.registerExpand(BVUSUBO, BitvectorRules::expandBvUSubO);
		checker.registerExpand(BVSSUBO, BitvectorRules::expandBvSSubO);
		checker.registerExpand(BVNOT, BitvectorRules::expandBvNot);
		checker.registerExpand(BVAND, BitvectorRules::expandBvAnd);
		checker.registerExpand(BVOR, BitvectorRules::expandBvOr);
		checker.registerExpand(BVXOR, BitvectorRules::expandBvXor);
		checker.registerExpand(BVNAND, BitvectorRules::expandBvNAnd);
		checker.registerExpand(BVNOR, BitvectorRules::expandBvNOr);
		checker.registerExpand(BVXNOR, BitvectorRules::expandBvXnor);
		checker.registerExpand(BVULE, BitvectorRules::expandBvLessGreater);
		checker.registerExpand(BVULT, BitvectorRules::expandBvLessGreater);
		checker.registerExpand(BVUGE, BitvectorRules::expandBvLessGreater);
		checker.registerExpand(BVUGT, BitvectorRules::expandBvLessGreater);
		checker.registerExpand(BVSLE, BitvectorRules::expandBvLessGreater);
		checker.registerExpand(BVSLT, BitvectorRules::expandBvLessGreater);
		checker.registerExpand(BVSGE, BitvectorRules::expandBvLessGreater);
		checker.registerExpand(BVSGT, BitvectorRules::expandBvLessGreater);
		checker.registerExpand(BVCOMP, BitvectorRules::expandBvComp);
		checker.registerExpand(CONCAT, BitvectorRules::expandConcat);
		checker.registerExpand(EXTRACT, BitvectorRules::expandExtract);
		checker.registerExpand(REPEAT, BitvectorRules::expandRepeat);
		checker.registerExpand(SIGN_EXTEND, BitvectorRules::expandSignExtend);
		checker.registerExpand(ZERO_EXTEND, BitvectorRules::expandZeroExtend);
		checker.registerExpand(ROTATE_LEFT, BitvectorRules::expandRotateLeft);
		checker.registerExpand(ROTATE_RIGHT, BitvectorRules::expandRotateRight);
	}

	/**
	 * Expand `(bvadd a1 ...)` to `((_int_to_bv k) (+ (ubv_to_int a1) ...)
	 *
	 * @param args the arguments of the bvadd.
	 * @return the expanded term.
	 */
	public static Term expandBvAdd(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVADD;
		assert args.length >= 2;
		final Theory theory = args[0].getTheory();
		final Term[] convArgs = new Term[args.length];
		for (int i = 0; i < convArgs.length; i++) {
			convArgs[i] = theory.term(UBV_TO_INT, args[i]);
		}
		final Term plusTerm = theory.term(PLUS, convArgs);
		return theory.term(INT_TO_BV, args[0].getSort().getIndices(), null, plusTerm);
	}

	/**
	 * Expand `(bvsub a1 ...)` to `((_int_to_bv k) (+ (ubv_to_int a1) (* (- 1)
	 * ...)))`.
	 *
	 * @param args the arguments of the bvsub.
	 * @return the expanded term.
	 */
	public static Term expandBvSub(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVSUB;
		assert args.length >= 2;
		final Theory theory = args[0].getTheory();
		final Term minusOne = Rational.MONE.toTerm(theory.getSort(INT));
		final Term[] convArgs = new Term[args.length];
		convArgs[0] = theory.term(UBV_TO_INT, args[0]);
		for (int i = 1; i < convArgs.length; i++) {
			convArgs[i] = theory.term(MUL, minusOne, theory.term(UBV_TO_INT, args[i]));
		}
		final Term plusTerm = theory.term(PLUS, convArgs);
		return theory.term(INT_TO_BV, args[0].getSort().getIndices(), null, plusTerm);
	}

	/**
	 * Expand `(bvmul a1 ...)` to `((_int_to_bv k) (* (ubv_to_int a1) ...)
	 *
	 * @param args the arguments of the bvmul.
	 * @return the expanded term.
	 */
	public static Term expandBvMul(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVMUL;
		assert args.length >= 2;
		final Theory theory = args[0].getTheory();
		final Term[] convArgs = new Term[args.length];
		for (int i = 0; i < convArgs.length; i++) {
			convArgs[i] = theory.term(UBV_TO_INT, args[i]);
		}
		final Term plusTerm = theory.term(MUL, convArgs);
		return theory.term(INT_TO_BV, args[0].getSort().getIndices(), null, plusTerm);
	}

	/**
	 * Expand `(bvudiv x y)` to `((_ int_to_bv k) (ite (= (ubv_to_int y) 0) (- 1)
	 * (div (ubv_to_int x) (ubv_to_int y)))))`
	 *
	 * @param args the arguments of the bvudiv.
	 * @return the expanded term.
	 */
	public static Term expandBvUdiv(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVUDIV;
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		final Term dividend = theory.term(UBV_TO_INT, args[0]);
		final Term divisor = theory.term(UBV_TO_INT, args[1]);
		final Term zero = Rational.ZERO.toTerm(divisor.getSort());
		final Term mone = Rational.MONE.toTerm(divisor.getSort());
		final Term result = theory.term(ITE, theory.term(EQUALS, divisor, zero), mone,
				theory.term(DIV, dividend, divisor));
		return theory.term(INT_TO_BV, args[0].getSort().getIndices(), null, result);
	}

	/**
	 * Expand `(bvurem x y)` to `(ite (= (ubv_to_int y) 0) x ((_ int_to_bv k) (mod
	 * (ubv_to_int x) (ubv_to_int y)))))`
	 *
	 * @param args the arguments of the bvurem.
	 * @return the expanded term.
	 */
	public static Term expandBvUrem(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVUREM;
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		final Term dividend = theory.term(UBV_TO_INT, args[0]);
		final Term divisor = theory.term(UBV_TO_INT, args[1]);
		final Term zero = Rational.ZERO.toTerm(divisor.getSort());
		final Term modulo = theory.term(MOD, dividend, divisor);
		return theory.term(ITE, theory.term(EQUALS, divisor, zero), args[0],
				theory.term(INT_TO_BV, args[0].getSort().getIndices(), null, modulo));
	}

	/**
	 * Expand {@code (bvsdiv x y)} to
	 *
	 * <pre>{@code
	 *    (let ((ix (sbv_to_int x)) (iy (sbv_to_int y)))
	 *       ((_ int_to_bv k) (ite (< ix 0)
	 *            (ite (< iy 0) (div (* (- 1) ix) (* (- 1) iy)) (ite (= iy 0) 1 (* (- 1) (div (* (- 1) ix) iy))))
	 *            (ite (< iy 0) (* (- 1) (div ix (* (- 1) iy))) (ite (= iy 0) (- 1) (div ix iy)))))))
	 * }</pre>
	 *
	 * @param f the function symbol bvsdiv.
	 * @param args the arguments of the bvsdiv.
	 * @return the expanded term.
	 */
	public static Term expandBvSdiv(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVSDIV;
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		final Term dividend = theory.term(SBV_TO_INT, args[0]);
		final Term divisor = theory.term(SBV_TO_INT, args[1]);
		final Term zero = Rational.ZERO.toTerm(divisor.getSort());
		final Term one = Rational.ONE.toTerm(divisor.getSort());
		final Term mone = Rational.MONE.toTerm(divisor.getSort());
		final Term negDividend = theory.term(MUL, mone, dividend);
		final Term negDivisor = theory.term(MUL, mone, divisor);
		final Term xNegCase = theory.term(ITE, theory.term(LT, divisor, zero),
				theory.term(DIV, negDividend, negDivisor),
				theory.term(ITE, theory.term(EQUALS, divisor, zero), one,
						theory.term(MUL, mone, theory.term(DIV, negDividend, divisor))));
		final Term xPosCase = theory.term(ITE, theory.term(LT, divisor, zero),
				theory.term(MUL, mone, theory.term(DIV, dividend, negDivisor)),
				theory.term(ITE, theory.term(EQUALS, divisor, zero), mone,
						theory.term(DIV, dividend, divisor)));
		final Term result = theory.term(ITE, theory.term(LT, dividend, zero), xNegCase, xPosCase);
		return theory.term(INT_TO_BV, args[0].getSort().getIndices(), null, result);
	}

	/**
	 * Expand {@code (bvsrem x y)} to
	 *
	 * <pre>{@code
	 *    (let ((ix (sbv_to_int x)) (iy (sbv_to_int y)))
	 *        ((_ int_to_bv k) (ite (= iy 0) ix
	 *            (ite (< ix 0) (- (mod (- ix) iy)) (mod ix iy))))))
	 * }</pre>
	 *
	 * @param f    the function symbol bvsrem.
	 * @param args the arguments of the bvsrem.
	 * @return the expanded term.
	 */
	public static Term expandBvSrem(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVSREM;
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		final Term dividend = theory.term(SBV_TO_INT, args[0]);
		final Term divisor = theory.term(SBV_TO_INT, args[1]);
		final Term zero = Rational.ZERO.toTerm(divisor.getSort());
		final Term mone = Rational.MONE.toTerm(divisor.getSort());
		final Term xNegCase = theory.term(MUL, mone, theory.term(MOD, theory.term(MUL, mone, dividend), divisor));
		final Term xPosCase = theory.term(MOD, dividend, divisor);
		final Term result = theory.term(ITE, theory.term(EQUALS, divisor, zero), dividend,
				theory.term(ITE, theory.term(LT, dividend, zero), xNegCase, xPosCase));
		return theory.term(INT_TO_BV, args[0].getSort().getIndices(), null, result);
	}

	/**
	 * Expand {@code (bvsmod x y)} to
	 *
	 * <pre>{@code
	 *    (let ((ix (sbv_to_int x)) (iy (sbv_to_int y)))
	 *       ((_ int_to_bv k) (ite (= iy 0) ix (ite (< iy 0) (+ (mod (+ ix (- 1)) iy) iy 1) (mod ix iy)))))
	 * }</pre>
	 *
	 * So the sign of the modulo matches the sign of the divisor, not the sign of
	 * the dividend.
	 *
	 * @param f    the function symbol bvsmod.
	 * @param args the arguments of the bvsmod.
	 * @return the expanded term.
	 */
	public static Term expandBvSmod(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVSMOD;
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		final Term dividend = theory.term(SBV_TO_INT, args[0]);
		final Term divisor = theory.term(SBV_TO_INT, args[1]);
		final Term zero = Rational.ZERO.toTerm(divisor.getSort());
		final Term one = Rational.MONE.toTerm(divisor.getSort());
		final Term mone = Rational.MONE.toTerm(divisor.getSort());
		final Term yNegCase = theory.term(PLUS,
				theory.term(MOD, theory.term(PLUS, dividend, mone), divisor), divisor, one);
		final Term yPosCase = theory.term(MOD, dividend, divisor);
		final Term result = theory.term(ITE, theory.term(EQUALS, divisor, zero), dividend,
				theory.term(ITE, theory.term(LT, divisor, zero), yNegCase, yPosCase));
		return theory.term(INT_TO_BV, args[0].getSort().getIndices(), null, result);
	}

	/**
	 * Expand `(bvneg a)` to `((_int_to_bv k) (* (- 1) (ubv_to_int a1)))`.
	 *
	 * @param arg the argument of the bvneg.
	 * @return the expanded term.
	 */
	public static Term expandBvNeg(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVNEG;
		assert args.length == 1;
		final Term arg = args[0];
		final Theory theory = arg.getTheory();
		final Term minusOne = Rational.MONE.toTerm(theory.getSort(INT));
		final Term convArg = theory.term(MUL, minusOne, theory.term(UBV_TO_INT, arg));
		return theory.term(INT_TO_BV, arg.getSort().getIndices(), null, convArg);
	}

	/**
	 * Expand {@code (bvnego x)} to {@code (= (ubv_to_int x) 2^k-1)}.
	 *
	 * @param f    the function symbol bvnego.
	 * @param args the arguments of the bvnego.
	 * @return the expanded term.
	 */
	public static Term expandBvNegO(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVNEGO;
		assert args.length == 1;
		final Theory theory = args[0].getTheory();
		final Term arg = theory.term(SBV_TO_INT, args[0]);
		final int bitLength = Integer.parseInt(args[0].getSort().getIndices()[0]);
		final Rational signBit = Rational.valueOf(BigInteger.ONE.shiftLeft(bitLength - 1), BigInteger.ONE).negate();
		return theory.term(EQUALS, arg, signBit.toTerm(arg.getSort()));
	}

	/**
	 * Expand {@code (bvuaddo x y)} to
	 * {@code (<= 2^k (+ (ubv_to_int x) (ubv_to_int y))}.
	 *
	 * @param f    the function symbol bvuaddo.
	 * @param args the arguments of the bvuaddo.
	 * @return the expanded term.
	 */
	public static Term expandBvUAddO(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVUADDO;
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		final int bitLength = Integer.parseInt(args[0].getSort().getIndices()[0]);
		final Term arg0 = theory.term(UBV_TO_INT, args[0]);
		final Term arg1 = theory.term(UBV_TO_INT, args[1]);
		final Rational pow2 = Rational.valueOf(BigInteger.ONE.shiftLeft(bitLength), BigInteger.ONE);
		return theory.term(LEQ, pow2.toTerm(arg0.getSort()), theory.term(PLUS, arg0, arg1));
	}

	/**
	 * Expand {@code (bvsaddo x y)} to
	 * {@code (or (< (+ (sbv_to_int x) (sbv_to_int y) -2^k-1) (<= 2^k-1 (+ (sbv_to_int x) (sbv_to_int y))}.
	 *
	 * @param f    the function symbol bvsaddo.
	 * @param args the arguments of the bvsaddo.
	 * @return the expanded term.
	 */
	public static Term expandBvSAddO(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVSADDO;
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		final int bitLength = Integer.parseInt(args[0].getSort().getIndices()[0]);
		final Term arg0 = theory.term(SBV_TO_INT, args[0]);
		final Term arg1 = theory.term(SBV_TO_INT, args[1]);
		final Term sum = theory.term(PLUS, arg0, arg1);
		final Rational maxInt = Rational.valueOf(BigInteger.ONE.shiftLeft(bitLength - 1), BigInteger.ONE);
		final Rational minInt = maxInt.negate();
		final Sort sort = arg0.getSort();
		return theory.term(OR, theory.term(LT, sum, minInt.toTerm(sort)), theory.term(LEQ, maxInt.toTerm(sort), sum));
	}

	/**
	 * Expand {@code (bvumulo x y)} to
	 * {@code (<= 2^k (* (ubv_to_int x) (ubv_to_int y))}.
	 *
	 * @param f    the function symbol bvumulo.
	 * @param args the arguments of the bvumulo.
	 * @return the expanded term.
	 */
	public static Term expandBvUMulO(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVUMULO;
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		final int bitLength = Integer.parseInt(args[0].getSort().getIndices()[0]);
		final Term arg0 = theory.term(UBV_TO_INT, args[0]);
		final Term arg1 = theory.term(UBV_TO_INT, args[1]);
		final Rational pow2 = Rational.valueOf(BigInteger.ONE.shiftLeft(bitLength), BigInteger.ONE);
		return theory.term(LEQ, pow2.toTerm(arg0.getSort()), theory.term(MUL, arg0, arg1));
	}

	/**
	 * Expand {@code (bvsmulo x y)} to
	 * {@code (or (< (* (sbv_to_int x) (sbv_to_int y) -2^k-1) (<= 2^k-1 (* (sbv_to_int x) (sbv_to_int y))}.
	 *
	 * @param f    the function symbol bvsmulo.
	 * @param args the arguments of the bvsmulo.
	 * @return the expanded term.
	 */
	public static Term expandBvSMulO(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVSMULO;
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		final int bitLength = Integer.parseInt(args[0].getSort().getIndices()[0]);
		final Term arg0 = theory.term(SBV_TO_INT, args[0]);
		final Term arg1 = theory.term(SBV_TO_INT, args[1]);
		final Term prod = theory.term(MUL, arg0, arg1);
		final Rational maxInt = Rational.valueOf(BigInteger.ONE.shiftLeft(bitLength - 1), BigInteger.ONE);
		final Rational minInt = maxInt.negate();
		final Sort sort = arg0.getSort();
		return theory.term(OR, theory.term(LT, prod, minInt.toTerm(sort)), theory.term(LEQ, maxInt.toTerm(sort), prod));
	}

	/**
	 * Expand {@code (bvdivo x y)} to
	 * {@code (and (= (sbv_to_int x) -2^k-1) (= (sbv_to_int y) (- 1))}.
	 *
	 * @param f    the function symbol bvdivo.
	 * @param args the arguments of the bvdivo.
	 * @return the expanded term.
	 */
	public static Term expandBvSDivO(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVSDIVO;
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		final Term arg0 = theory.term(SBV_TO_INT, args[0]);
		final Term arg1 = theory.term(SBV_TO_INT, args[1]);
		final int bitLength = Integer.parseInt(args[0].getSort().getIndices()[0]);
		final Rational signBit = Rational.valueOf(BigInteger.ONE.shiftLeft(bitLength - 1), BigInteger.ONE).negate();
		final Sort sort = arg0.getSort();
		return theory.term(AND, theory.term(EQUALS, arg0, signBit.toTerm(sort)),
				theory.term(EQUALS, arg1, Rational.MONE.toTerm(sort)));
	}

	/**
	 * Expand {@code (bvusubo x y)} to {@code (< (ubv_to_int x) (ubv_to_int y))}.
	 *
	 * @param f    the function symbol bvuaddo.
	 * @param args the arguments of the bvuaddo.
	 * @return the expanded term.
	 */
	public static Term expandBvUSubO(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVUSUBO;
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		final Term arg0 = theory.term(UBV_TO_INT, args[0]);
		final Term arg1 = theory.term(UBV_TO_INT, args[1]);
		return theory.term(LT, arg0, arg1);
	}

	/**
	 * Expand {@code (bvssubo x y)} to
	 * {@code (let ((diff (+ (sbv_to_int x) (* (- 1) (sbv_to_int y))))) (or (< diff -2^k-1) (<= 2^k-1 diff))) }.
	 *
	 * @param f    the function symbol bvsaddo.
	 * @param args the arguments of the bvsaddo.
	 * @return the expanded term.
	 */
	public static Term expandBvSSubO(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVSSUBO;
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		final int bitLength = Integer.parseInt(args[0].getSort().getIndices()[0]);
		final Term arg0 = theory.term(SBV_TO_INT, args[0]);
		final Term arg1 = theory.term(SBV_TO_INT, args[1]);
		final Sort sort = arg0.getSort();
		final Term mone = Rational.MONE.toTerm(sort);
		final Term diff = theory.term(PLUS, arg0, theory.term(MUL, mone, arg1));
		final Rational maxInt = Rational.valueOf(BigInteger.ONE.shiftLeft(bitLength - 1), BigInteger.ONE);
		final Rational minInt = maxInt.negate();
		return theory.term(OR, theory.term(LT, diff, minInt.toTerm(sort)), theory.term(LEQ, maxInt.toTerm(sort), diff));
	}

	private static Term buildIntegerNot(Term convTerm) {
		final Theory theory = convTerm.getTheory();
		final Term minusOne = Rational.MONE.toTerm(convTerm.getSort());
		final Term negTerm = theory.term(MUL, minusOne, convTerm);
		return theory.term(PLUS, minusOne, negTerm);
	}

	/**
	 * Expand `(bvnot a)` to `((_int_to_bv k) (+ (- 1) (* (- 1) (ubv_to_int a1)))`.
	 *
	 * @param arg the argument of the bvnot.
	 * @return the expanded term.
	 */
	public static Term expandBvNot(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVNOT;
		assert args.length == 1;
		final Term arg = args[0];
		final Theory theory = arg.getTheory();
		final Term plusTerm = buildIntegerNot(theory.term(UBV_TO_INT, arg));
		return theory.term(INT_TO_BV, arg.getSort().getIndices(), null, plusTerm);
	}

	/**
	 * Expand `(bvand a1 ...)` to `((_int_to_bv k) (& (ubv_to_int a1) ...)
	 *
	 * @param args the arguments of the bvand.
	 * @return the expanded term.
	 */
	public static Term expandBvAnd(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVAND;
		assert args.length >= 2;
		final Theory theory = args[0].getTheory();
		final Term[] convArgs = new Term[args.length];
		for (int i = 0; i < convArgs.length; i++) {
			convArgs[i] = theory.term(UBV_TO_INT, args[i]);
		}
		final Term andTerm = theory.term(SMTInterpolConstants.INTAND, convArgs);
		return theory.term(INT_TO_BV, args[0].getSort().getIndices(), null, andTerm);
	}

	private static Term buildOrXorPlus(Term[] args, Rational factor, Term andTerm) {
		final Theory theory = args[0].getTheory();
		final Term[] plusArgs = new Term[args.length + 1];
		System.arraycopy(args, 0, plusArgs, 0, args.length);
		plusArgs[args.length] = theory.term(MUL, factor.toTerm(andTerm.getSort()), andTerm);
		return theory.term(PLUS, plusArgs);
	}

	/**
	 * Expand `(bvor a1 ...)` to `((_int_to_bv k) (+ a1 ... (* (- 1) (& (ubv_to_int
	 * a1) ...))))`.
	 *
	 * @param args the arguments of the bvor.
	 * @return the expanded term.
	 */
	public static Term expandBvOr(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVOR;
		assert args.length >= 2;
		final Theory theory = args[0].getTheory();
		final Term[] convArgs = new Term[args.length];
		for (int i = 0; i < convArgs.length; i++) {
			convArgs[i] = theory.term(UBV_TO_INT, args[i]);
		}
		final Term andTerm = theory.term(SMTInterpolConstants.INTAND, convArgs);
		final Term plusTerm = buildOrXorPlus(convArgs, Rational.MONE, andTerm);
		return theory.term(INT_TO_BV, args[0].getSort().getIndices(), null, plusTerm);
	}

	/**
	 * Expand `(bvxor a1 ...)` to `((_int_to_bv k) (+ a1 ... (* (- 2) (& (ubv_to_int
	 * a1) ...))))`.
	 *
	 * @param args the arguments of the bvxor.
	 * @return the expanded term.
	 */
	public static Term expandBvXor(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVXOR;
		assert args.length >= 2;
		final Theory theory = args[0].getTheory();
		final Term[] convArgs = new Term[args.length];
		for (int i = 0; i < convArgs.length; i++) {
			convArgs[i] = theory.term(UBV_TO_INT, args[i]);
		}
		final Term andTerm = theory.term(SMTInterpolConstants.INTAND, convArgs);
		final Term plusTerm = buildOrXorPlus(convArgs, Rational.valueOf(-2, 1), andTerm);
		return theory.term(INT_TO_BV, args[0].getSort().getIndices(), null, plusTerm);
	}

	/**
	 * Expand `(bvnand a1 a2)` to `(bvnot (bvand a1 a2))`
	 *
	 * @param args the arguments of the bvnand.
	 * @return the expanded term.
	 */
	public static Term expandBvNAnd(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVNAND;
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		return theory.term(BVNOT, theory.term(BVAND, args));
	}

	/**
	 * Expand `(bvnor a1 a2)` to `(bvnot (bvor a1 a2))`
	 *
	 * @param args the arguments of the bvnand.
	 * @return the expanded term.
	 */
	public static Term expandBvNOr(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVNOR;
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		return theory.term(BVNOT, theory.term(BVOR, args));
	}

	/**
	 * Expand `(bvxnor a1 a2)` to `(bvnot (bvxor a1 a2))`
	 *
	 * @param args the arguments of the bvnand.
	 * @return the expanded term.
	 */
	public static Term expandBvXnor(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVXNOR;
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		return theory.term(BVNOT, theory.term(BVXOR, args));
	}

	/**
	 * Expand `(bvule a1 a2)` to `(<= (ubv_to_int a1) (ubv_to_int a2))` and similar.
	 *
	 * @param f    the function symbol to convert, must be one of bvule, bvult,
	 *             bvuge, bvugt, bvsle, bvslt, bvsge, bvsgt.
	 * @param args the arguments of the comparison operator.
	 * @return the expanded term.
	 */
	public static Term expandBvLessGreater(FunctionSymbol f, Term... args) {
		assert f.isIntern();
		assert args.length >= 2;
		boolean signed;
		final boolean isGt;
		final boolean strict;
		switch (f.getName()) {
		case BVULE:
			signed = false;
			strict = false;
			isGt = false;
			break;
		case BVULT:
			signed = false;
			strict = true;
			isGt = false;
			break;
		case BVUGE:
			signed = false;
			strict = false;
			isGt = true;
			break;
		case BVUGT:
			signed = false;
			strict = true;
			isGt = true;
			break;
		case BVSLE:
			signed = true;
			strict = false;
			isGt = false;
			break;
		case BVSLT:
			signed = true;
			strict = true;
			isGt = false;
			break;
		case BVSGE:
			signed = true;
			strict = false;
			isGt = true;
			break;
		case BVSGT:
			signed = true;
			strict = true;
			isGt = true;
			break;
		default:
			throw new AssertionError();
		}
		final Theory theory = args[0].getTheory();
		final Term[] convArgs = new Term[args.length];
		for (int i = 0; i < convArgs.length; i++) {
			convArgs[i] = theory.term(signed ? SBV_TO_INT : UBV_TO_INT, args[isGt ? 1 - i : i]);
		}
		return theory.term(strict ? LT : LEQ, convArgs);
	}

	public static Term expandBvComp(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVCOMP;
		final Theory theory = args[0].getTheory();
		// bit comparator: equals #b1 iff all bits are equal
		final Sort bvSort1 = theory.getSort(BITVEC, new String[] { "1" });
		return theory.term(ITE, theory.term(EQUALS, args[0], args[1]), theory.constant(BigInteger.ONE, bvSort1),
				theory.constant(BigInteger.ZERO, bvSort1));
	}

	/**
	 * Expand `(concat a1 .. an)` to `((_int_to_bv k) (+ (* 2^... (ubv_to_int a1))
	 * ...)
	 *
	 * @param args the arguments of the bvand.
	 * @return the expanded term.
	 */
	public static Term expandConcat(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == CONCAT;
		assert args.length >= 2;
		final Theory theory = args[0].getTheory();
		final Term[] convArgs = new Term[args.length];
		int shift = 0;
		for (int i = convArgs.length - 1; i >= 0; i--) {
			Term intArg = theory.term(UBV_TO_INT, args[i]);
			if (shift > 0) {
				final Rational pow2 = Rational.valueOf(BigInteger.ONE.shiftLeft(shift), BigInteger.ONE);
				intArg = theory.term(MUL, pow2.toTerm(intArg.getSort()), intArg);
			}
			convArgs[i] = intArg;
			shift += Integer.parseInt(args[i].getSort().getIndices()[0]);
		}
		final Term plusTerm = theory.term(PLUS, convArgs);
		return theory.term(INT_TO_BV, new String[] { Integer.toString(shift) }, null, plusTerm);
	}

	/**
	 * Expand `((_ extract j i) a)` to `((_ int_to_bv j-i+1) (+ (div (ubv_to_int
	 * a1)) 2^i)
	 *
	 * @param args the arguments of the bvand.
	 * @return the expanded term.
	 */
	public static Term expandExtract(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == EXTRACT;
		final int high = Integer.parseInt(f.getIndices()[0]);
		final int low = Integer.parseInt(f.getIndices()[1]);
		assert high >= low && low >= 0;
		assert args.length == 1;
		final Term arg = args[0];
		final Theory theory = arg.getTheory();
		final int size = high - low + 1;
		Term intArg = theory.term(UBV_TO_INT, arg);
		final Rational pow2 = Rational.valueOf(BigInteger.ONE.shiftLeft(low), BigInteger.ONE);
		intArg = theory.term(DIV, intArg, pow2.toTerm(intArg.getSort()));

		return theory.term(INT_TO_BV, new String[] { Integer.toString(size) }, null, intArg);
	}

	/**
	 * Expand `((_ repeat j) a)` to `((_ int_to_bv j*k) (* (2^(j*k)/2^k) (ubv_to_int
	 * a)))`
	 *
	 * @param args the arguments of the bvand.
	 * @return the expanded term.
	 */
	public static Term expandRepeat(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == REPEAT;
		final int count = Integer.parseInt(f.getIndices()[0]);
		assert args.length == 1;
		final Term arg = args[0];
		final Theory theory = arg.getTheory();
		final int bitlen = Integer.valueOf(arg.getSort().getIndices()[0]);
		final int targetlen = bitlen * count;
		final BigInteger magicMultiplier = BigInteger.ONE.shiftLeft(targetlen).subtract(BigInteger.ONE)
				.divide(BigInteger.ONE.shiftLeft(bitlen).subtract(BigInteger.ONE));
		final Term intArg = theory.term(UBV_TO_INT, arg);
		final Term magicTerm = Rational.valueOf(magicMultiplier, BigInteger.ONE).toTerm(intArg.getSort());
		final Term result = theory.term(MUL, magicTerm, intArg);
		return theory.term(INT_TO_BV, new String[] { Integer.toString(targetlen) }, null, result);
	}

	/**
	 * Expand `((_ sign_extend j) a)` to `((_ int_to_bv j+k) (sbv_to_int a1))`.
	 *
	 * @param newBits the index of the sign_extend.
	 * @param arg     the arguments of the sign_extend.
	 * @return the expanded term.
	 */
	public static Term expandSignExtend(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == SIGN_EXTEND;
		final int newBits = Integer.parseInt(f.getIndices()[0]);
		assert newBits > 0;
		assert args.length == 1;
		final Term arg = args[0];
		final Theory theory = arg.getTheory();
		final int oldSize = Integer.parseInt(arg.getSort().getIndices()[0]);
		final int size = oldSize + newBits;
		final Term intArg = theory.term(SBV_TO_INT, arg);
		return theory.term(INT_TO_BV, new String[] { Integer.toString(size) }, null, intArg);
	}

	/**
	 * Expand `((_ zero_extend j) a)` to `((_ int_to_bv j+k) (ubv_to_int a1))`.
	 *
	 * @param newBits the index of the zero_extend.
	 * @param arg     the arguments of the zero_extend.
	 * @return the expanded term.
	 */
	public static Term expandZeroExtend(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == ZERO_EXTEND;
		final int newBits = Integer.parseInt(f.getIndices()[0]);
		assert newBits > 0;
		assert args.length == 1;
		final Term arg = args[0];
		final Theory theory = arg.getTheory();
		final int oldSize = Integer.parseInt(arg.getSort().getIndices()[0]);
		final int size = oldSize + newBits;
		final Term intArg = theory.term(UBV_TO_INT, arg);
		return theory.term(INT_TO_BV, new String[] { Integer.toString(size) }, null, intArg);
	}

	private static Term rotate(int leftShift, int rightShift, Term arg) {
		final Theory theory = arg.getTheory();
		final Term intArg = theory.term(UBV_TO_INT, arg);
		final Rational pow2Left = Rational.valueOf(BigInteger.ONE.shiftLeft(leftShift), BigInteger.ONE);
		final Rational pow2Right = Rational.valueOf(BigInteger.ONE.shiftLeft(rightShift), BigInteger.ONE);
		final Term shiftedLeft = theory.term(MUL, pow2Left.toTerm(intArg.getSort()), intArg);
		final Term shiftedRight = theory.term(DIV, intArg, pow2Right.toTerm(intArg.getSort()));
		final Term result = theory.term(PLUS, shiftedLeft, shiftedRight);
		final int size = leftShift + rightShift;
		return theory.term(INT_TO_BV, new String[] { Integer.toString(size) }, null, result);
	}

	/**
	 * Expand {@code ((_ rotate_left j) a)} to
	 * {@code ((_ int_to_bv k) (+ (* 2^j (ubv_to_int a))
	 * (div (ubv_to_int a) 2^(k-j))))}.
	 *
	 * @param newBits the index of the rotate_left.
	 * @param arg     the arguments of the rotate_left.
	 * @return the expanded term.
	 */
	public static Term expandRotateLeft(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == ROTATE_LEFT;
		final int cnt = Integer.parseInt(f.getIndices()[0]);
		assert args.length == 1;
		final int bitSize = Integer.parseInt(args[0].getSort().getIndices()[0]);
		return rotate(cnt, bitSize - cnt, args[0]);
	}

	/**
	 * Expand {@code ((_ rotate_right j) a)} to
	 * {@code ((_ int_to_bv k) (+ (* 2^(k-j)
	 * (ubv_to_int a)) (div (ubv_to_int a) 2^j)))}.
	 *
	 * @param newBits the index of the rotate_right.
	 * @param arg     the arguments of the rotate_right.
	 * @return the expanded term.
	 */
	public static Term expandRotateRight(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == ROTATE_RIGHT;
		final int cnt = Integer.parseInt(f.getIndices()[0]);
		assert args.length == 1;
		final int bitSize = Integer.parseInt(args[0].getSort().getIndices()[0]);
		return rotate(bitSize - cnt, cnt, args[0]);
	}
}
