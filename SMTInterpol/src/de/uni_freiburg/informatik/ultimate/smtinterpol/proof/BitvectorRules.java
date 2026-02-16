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

import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVADD;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVAND;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVMUL;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVNAND;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVNEG;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVNOT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVOR;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVSUB;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVUDIV;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVUREM;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.BVXOR;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.CONCAT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.DIV;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.EQUALS;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.EXTRACT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.INT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.INT_TO_BV;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.ITE;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.MOD;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.MUL;
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
		checker.registerExpand(BVMUL, BitvectorRules::expandBvMul);
		checker.registerExpand(BVUDIV, BitvectorRules::expandBvUdiv);
		checker.registerExpand(BVUREM, BitvectorRules::expandBvUrem);
		checker.registerExpand(BVNEG, BitvectorRules::expandBvNeg);
		checker.registerExpand(BVNOT, BitvectorRules::expandBvNot);
		checker.registerExpand(BVAND, BitvectorRules::expandBvAnd);
		checker.registerExpand(BVOR, BitvectorRules::expandBvOr);
		checker.registerExpand(BVXOR, BitvectorRules::expandBvXor);
		checker.registerExpand(BVNAND, BitvectorRules::expandBvNAnd);
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
	 * Expand `(bvnand a1 ...)` to `((_int_to_bv k) (+ (- 1) (* (- 1) (& (ubv_to_int
	 * a1) ...))))`
	 *
	 * @param args the arguments of the bvnand.
	 * @return the expanded term.
	 */
	public static Term expandBvNAnd(FunctionSymbol f, Term... args) {
		assert f.isIntern() && f.getName() == BVNAND;
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		final Term[] convArgs = new Term[args.length];
		for (int i = 0; i < convArgs.length; i++) {
			convArgs[i] = theory.term(UBV_TO_INT, args[i]);
		}
		final Term andTerm = theory.term(SMTInterpolConstants.INTAND, convArgs);
		return theory.term(INT_TO_BV, args[0].getSort().getIndices(), null, buildIntegerNot(andTerm));
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
