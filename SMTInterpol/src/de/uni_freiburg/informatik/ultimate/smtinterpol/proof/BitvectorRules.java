package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;

/**
 * Helper class to expand bitvector operations.
 */
public class BitvectorRules {
	/**
	 * Expand `(bvadd a1 ...)` to `((_int_to_bv k) (+ (ubv_to_int a1) ...)
	 *
	 * @param args the arguments of the bvadd.
	 * @return the expanded term.
	 */
	public static Term expandBvAdd(Term... args) {
		assert args.length >= 2;
		final Theory theory = args[0].getTheory();
		final Term[] convArgs = new Term[args.length];
		for (int i = 0; i < convArgs.length; i++) {
			convArgs[i] = theory.term(SMTLIBConstants.UBV_TO_INT, args[i]);
		}
		final Term plusTerm = theory.term(SMTLIBConstants.PLUS, convArgs);
		return theory.term(SMTLIBConstants.INT_TO_BV, args[0].getSort().getIndices(), null, plusTerm);
	}

	/**
	 * Expand `(bvsub a1 ...)` to `((_int_to_bv k) (+ (ubv_to_int a1) (* (- 1)
	 * ...)))`.
	 *
	 * @param args the arguments of the bvsub.
	 * @return the expanded term.
	 */
	public static Term expandBvSub(Term... args) {
		assert args.length >= 2;
		final Theory theory = args[0].getTheory();
		final Term minusOne = Rational.MONE.toTerm(theory.getSort(SMTLIBConstants.INT));
		final Term[] convArgs = new Term[args.length];
		convArgs[0] = theory.term(SMTLIBConstants.UBV_TO_INT, args[0]);
		for (int i = 1; i < convArgs.length; i++) {
			convArgs[i] = theory.term(SMTLIBConstants.MUL, minusOne, theory.term(SMTLIBConstants.UBV_TO_INT, args[i]));
		}
		final Term plusTerm = theory.term(SMTLIBConstants.PLUS, convArgs);
		return theory.term(SMTLIBConstants.INT_TO_BV, args[0].getSort().getIndices(), null, plusTerm);
	}

	/**
	 * Expand `(bvmul a1 ...)` to `((_int_to_bv k) (* (ubv_to_int a1) ...)
	 *
	 * @param args the arguments of the bvmul.
	 * @return the expanded term.
	 */
	public static Term expandBvMul(Term... args) {
		assert args.length >= 2;
		final Theory theory = args[0].getTheory();
		final Term[] convArgs = new Term[args.length];
		for (int i = 0; i < convArgs.length; i++) {
			convArgs[i] = theory.term(SMTLIBConstants.UBV_TO_INT, args[i]);
		}
		final Term plusTerm = theory.term(SMTLIBConstants.MUL, convArgs);
		return theory.term(SMTLIBConstants.INT_TO_BV, args[0].getSort().getIndices(), null, plusTerm);
	}

	/**
	 * Expand `(bvneg a)` to `((_int_to_bv k) (* (- 1) (ubv_to_int a1)))`.
	 *
	 * @param arg the argument of the bvneg.
	 * @return the expanded term.
	 */
	public static Term expandBvNeg(Term arg) {
		final Theory theory = arg.getTheory();
		final Term minusOne = Rational.MONE.toTerm(theory.getSort(SMTLIBConstants.INT));
		final Term convArg = theory.term(SMTLIBConstants.MUL, minusOne, theory.term(SMTLIBConstants.UBV_TO_INT, arg));
		return theory.term(SMTLIBConstants.INT_TO_BV, arg.getSort().getIndices(), null, convArg);
	}

	private static Term buildIntegerNot(Term convTerm) {
		final Theory theory = convTerm.getTheory();
		final Term minusOne = Rational.MONE.toTerm(convTerm.getSort());
		final Term negTerm = theory.term(SMTLIBConstants.MUL, minusOne, convTerm);
		return theory.term(SMTLIBConstants.PLUS, minusOne, negTerm);
	}

	/**
	 * Expand `(bvnot a)` to `((_int_to_bv k) (+ (- 1) (* (- 1) (ubv_to_int a1)))`.
	 *
	 * @param arg the argument of the bvnot.
	 * @return the expanded term.
	 */
	public static Term expandBvNot(Term arg) {
		final Theory theory = arg.getTheory();
		final Term plusTerm = buildIntegerNot(theory.term(SMTLIBConstants.UBV_TO_INT, arg));
		return theory.term(SMTLIBConstants.INT_TO_BV, arg.getSort().getIndices(), null, plusTerm);
	}

	/**
	 * Expand `(bvand a1 ...)` to `((_int_to_bv k) (& (ubv_to_int a1) ...)
	 *
	 * @param args the arguments of the bvand.
	 * @return the expanded term.
	 */
	public static Term expandBvAnd(Term... args) {
		assert args.length >= 2;
		final Theory theory = args[0].getTheory();
		final Term[] convArgs = new Term[args.length];
		for (int i = 0; i < convArgs.length; i++) {
			convArgs[i] = theory.term(SMTLIBConstants.UBV_TO_INT, args[i]);
		}
		final Term andTerm = theory.term(SMTInterpolConstants.INTAND, convArgs);
		return theory.term(SMTLIBConstants.INT_TO_BV, args[0].getSort().getIndices(), null, andTerm);
	}

	private static Term buildOrXorPlus(Term[] args, Rational factor, Term andTerm) {
		final Theory theory = args[0].getTheory();
		final Term[] plusArgs = new Term[args.length + 1];
		System.arraycopy(args, 0, plusArgs, 0, args.length);
		plusArgs[args.length] = theory.term(SMTLIBConstants.MUL, factor.toTerm(andTerm.getSort()), andTerm);
		return theory.term(SMTLIBConstants.PLUS, plusArgs);
	}

	/**
	 * Expand `(bvor a1 ...)` to `((_int_to_bv k) (+ a1 ... (* (- 1) (& (ubv_to_int
	 * a1) ...))))`.
	 *
	 * @param args the arguments of the bvor.
	 * @return the expanded term.
	 */
	public static Term expandBvOr(Term... args) {
		assert args.length >= 2;
		final Theory theory = args[0].getTheory();
		final Term[] convArgs = new Term[args.length];
		for (int i = 0; i < convArgs.length; i++) {
			convArgs[i] = theory.term(SMTLIBConstants.UBV_TO_INT, args[i]);
		}
		final Term andTerm = theory.term(SMTInterpolConstants.INTAND, convArgs);
		final Term plusTerm = buildOrXorPlus(convArgs, Rational.MONE, andTerm);
		return theory.term(SMTLIBConstants.INT_TO_BV, args[0].getSort().getIndices(), null, plusTerm);
	}

	/**
	 * Expand `(bvxor a1 ...)` to `((_int_to_bv k) (+ a1 ... (* (- 2) (& (ubv_to_int
	 * a1) ...))))`.
	 *
	 * @param args the arguments of the bvxor.
	 * @return the expanded term.
	 */
	public static Term expandBvXor(Term... args) {
		assert args.length >= 2;
		final Theory theory = args[0].getTheory();
		final Term[] convArgs = new Term[args.length];
		for (int i = 0; i < convArgs.length; i++) {
			convArgs[i] = theory.term(SMTLIBConstants.UBV_TO_INT, args[i]);
		}
		final Term andTerm = theory.term(SMTInterpolConstants.INTAND, convArgs);
		final Term plusTerm = buildOrXorPlus(convArgs, Rational.valueOf(-2, 1), andTerm);
		return theory.term(SMTLIBConstants.INT_TO_BV, args[0].getSort().getIndices(), null, plusTerm);
	}

	/**
	 * Expand `(bvnand a1 ...)` to `((_int_to_bv k) (+ (- 1) (* (- 1) (& (ubv_to_int
	 * a1) ...))))`
	 *
	 * @param args the arguments of the bvnand.
	 * @return the expanded term.
	 */
	public static Term expandBvNAnd(Term... args) {
		assert args.length == 2;
		final Theory theory = args[0].getTheory();
		final Term[] convArgs = new Term[args.length];
		for (int i = 0; i < convArgs.length; i++) {
			convArgs[i] = theory.term(SMTLIBConstants.UBV_TO_INT, args[i]);
		}
		final Term andTerm = theory.term(SMTInterpolConstants.INTAND, convArgs);
		return theory.term(SMTLIBConstants.INT_TO_BV, args[0].getSort().getIndices(), null,
				buildIntegerNot(andTerm));
	}

	/**
	 * Expand `(concat a1 .. an)` to `((_int_to_bv k) (+ (* 2^... (ubv_to_int a1))
	 * ...)
	 *
	 * @param args the arguments of the bvand.
	 * @return the expanded term.
	 */
	public static Term expandConcat(Term... args) {
		assert args.length >= 2;
		final Theory theory = args[0].getTheory();
		final Term[] convArgs = new Term[args.length];
		int shift = 0;
		for (int i = convArgs.length - 1; i >= 0; i--) {
			Term intArg = theory.term(SMTLIBConstants.UBV_TO_INT, args[i]);
			if (shift > 0) {
				final Rational pow2 = Rational.valueOf(BigInteger.ONE.shiftLeft(shift), BigInteger.ONE);
				intArg = theory.term(SMTLIBConstants.MUL, pow2.toTerm(intArg.getSort()), intArg);
			}
			convArgs[i] = intArg;
			shift += Integer.parseInt(args[i].getSort().getIndices()[0]);
		}
		final Term plusTerm = theory.term(SMTLIBConstants.PLUS, convArgs);
		return theory.term(SMTLIBConstants.INT_TO_BV, new String[] { Integer.toString(shift) }, null, plusTerm);
	}

	/**
	 * Expand `((_ extract j i) a)` to `((_int_to_bv j-i+1) (+ (div (ubv_to_int a1))
	 * 2^i)
	 *
	 * @param args the arguments of the bvand.
	 * @return the expanded term.
	 */
	public static Term expandExtract(int high, int low, Term arg) {
		assert high >= low && low >= 0;
		final Theory theory = arg.getTheory();
		final int size = high - low + 1;
		Term intArg = theory.term(SMTLIBConstants.UBV_TO_INT, arg);
		final Rational pow2 = Rational.valueOf(BigInteger.ONE.shiftLeft(low), BigInteger.ONE);
		intArg = theory.term(SMTLIBConstants.DIV, intArg, pow2.toTerm(intArg.getSort()));

		return theory.term(SMTLIBConstants.INT_TO_BV, new String[] { Integer.toString(size) }, null, intArg);
	}

}
