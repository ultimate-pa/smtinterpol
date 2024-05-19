package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.LogicSimplifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;

public class BvToIntUtils {

	private final Theory mTheory;
	private final LogicSimplifier mUtils;
	private final BvUtils mBvUtils;
	private final static String BITVEC_CONST_PATTERN = "bv\\d+";
	private final BvToIntProofTracker mProof;
	IProofTracker mTracker;
	boolean mEagerMod;
	boolean mDealWithBvToNatAndNatToBvInPreprocessing;

	public BvToIntUtils(final Theory theory, final LogicSimplifier utils, final BvUtils bvutils,
			final IProofTracker tracker, final boolean eagerMod,
			final boolean dealWithBvToNatAndNatToBvInPreprocessing) {
		mTheory = theory;
		mUtils = utils;
		mBvUtils = bvutils;
		mProof = new BvToIntProofTracker(theory, utils, bvutils, this);
		mTracker = tracker;
		mEagerMod = eagerMod;
		mDealWithBvToNatAndNatToBvInPreprocessing = dealWithBvToNatAndNatToBvInPreprocessing;
	}

	/*
	 * Deals with the uninterpreted function symbol bv2nat. Call this instead of theory.term("bv2nat", param); Does
	 * local simplifications, without using pushTerm to go throu the term again. Replaces bv2nat by a modulo in most
	 * cases
	 *
	 * At the end bv2nat should only be around uninterpreted functions (constants variables, selects, ...)
	 *
	 * TODO
	 *
	 * Case Switch, param is nat2bv (return param of nat2bv), param is constant,
	 *
	 */
	public Term bv2nat(final Term param, boolean mod) {
		assert param.getSort().isBitVecSort();
		// width of the first argument
		final BigInteger two = BigInteger.valueOf(2);
		// // maximal representable number by a bit-vector of width "width"
		if (mBvUtils.isConstRelation(param, null)) {
			if (param instanceof ConstantTerm) {
				return translateConstant(((ConstantTerm) param).getValue());
			} else {
				final BigInteger value = new BigInteger(((ApplicationTerm) param).getFunction().getName().substring(2));
				return translateConstant(value);
			}

		}
		if (param instanceof ApplicationTerm && mDealWithBvToNatAndNatToBvInPreprocessing) {
			final ApplicationTerm apParam = (ApplicationTerm) param;
			if (apParam.getFunction().getName().equals("nat2bv")) {
				if (mEagerMod) {
					if (apParam.getParameters()[0] instanceof ApplicationTerm) {
						if (mTheory.getDeclaredFunctions()
								.containsKey(((ApplicationTerm) apParam.getParameters()[0]).getFunction().getName())) {
							mod = true;
						}
					} else if (apParam.getParameters()[0] instanceof TermVariable) {
						mod = true;
					}
				}
				if (mod) {
					final int width = Integer.valueOf(apParam.getSort().getIndices()[0]);
					final Term maxNumber = mTheory.rational(Rational.valueOf(two.pow(width), BigInteger.ONE),
							mTheory.getSort(SMTLIBConstants.INT));
					return mTheory.term("mod", apParam.getParameters()[0], maxNumber);

				} else {
					return apParam.getParameters()[0];
				}
			}
			if (apParam.getFunction().getName().equals("ite")) {

				return mTheory.term("ite", apParam.getParameters()[0], bv2nat(apParam.getParameters()[1], mod),
						bv2nat(apParam.getParameters()[2], mod));
			}
		}
		return mTheory.term("bv2nat", param);
	}

	/*
	 * TODO RangeBased "nat2bv""bv2nat" -> mod,?
	 */
	public Term nat2bv(final Term param, final String[] width) {
		assert param.getSort().isNumericSort();
		// // TODO case switch for simplifications
		// // width of the first argument
		// final int widthInt = Integer.valueOf(width[0]);
		// final BigInteger two = BigInteger.valueOf(2);
		// // maximal representable number by a bit-vector of width "width"
		// final Term maxNumber = mTheory.rational(Rational.valueOf(two.pow(widthInt), BigInteger.ONE),
		// mTheory.getSort(SMTLIBConstants.INT));
		// // TODO optimize nat2bv nat2bv
		if (param instanceof ConstantTerm) {
			return translateConstantBack((Rational) ((ConstantTerm) param).getValue(), width);
			// return mTracker.reflexivity(translateConstantBack((Rational) ((ConstantTerm) param).getValue(), width));
		}
		// if (param instanceof ApplicationTerm) {
		// ApplicationTerm apParam = (ApplicationTerm) param;
		// if (apParam.getFunction().getName().equals("bv2nat")) {
		// if (width.equals(apParam.getParameters()[0].getSort().getIndices())) {
		// return apParam.getParameters()[0];
		//// return mTracker.reflexivity(apParam.getParameters()[0]);
		// }
		//
		// }
		// }
		return mTheory.term("nat2bv", width, null, param);
		// return mTracker.reflexivity(mTheory.term("nat2bv", width, null, param));
	}

	/*
	 * transforms a bitvector constant c to nat2bv(c')
	 */
	public Term translateBvConstant(final FunctionSymbol fsym, final Term convertedApp, final boolean eagerMod) {
		if (convertedApp.getSort().isBitVecSort()) {
			final BigInteger value = new BigInteger(fsym.getName().substring(2));
			return nat2bv(translateConstant(value), convertedApp.getSort().getIndices());
		} else {
			throw new UnsupportedOperationException("Can't convert bv constant: " + fsym.getName());
		}
	}

	/*
	 * transforms a bitvector constant c to nat2bv(c')
	 */
	public Term translateBvConstantTerm(final ConstantTerm term, final boolean eagerMod) {
		if (term.getSort().isBitVecSort()) {
			return nat2bv(translateConstant(term.getValue()), term.getSort().getIndices());
		} else {
			throw new UnsupportedOperationException("Can't convert bv constant: " + term);
		}
	}

	/*
	 * Gets as Input the value of a bit-vec const and returns an integer constant
	 */
	private Term translateConstant(final Object value) {
		final Sort intSort = mTheory.getSort(SMTLIBConstants.INT);
		BigInteger constValue;
		if (value instanceof String) {
			String bitString = (String) value;
			if (bitString.startsWith("#b")) {
				bitString = (String) value;
				constValue = new BigInteger(bitString.substring(2), 2);
			} else if (bitString.startsWith("#x")) {
				constValue = new BigInteger(bitString.substring(2), 16);
			} else {
				throw new UnsupportedOperationException("Unexpected constant type");
			}
		} else if (value instanceof BigInteger) {
			constValue = (BigInteger) value;
		} else {
			throw new UnsupportedOperationException("Unexpected constant type");
		}
		final Term intConst = mTheory.rational(Rational.valueOf(constValue, BigInteger.ONE), intSort);
		return intConst;
	}

	private Term translateConstantBack(final Rational value, final String[] width) {

		final Rational valueInRange = Rational
				.valueOf(value.numerator().mod(BigInteger.valueOf(2).pow(Integer.valueOf(width[0]))), BigInteger.ONE);
		return mTheory.term("bv" + valueInRange, width, null);

	}

	public Term translateTermVariable(final TermVariable term, final boolean mEagerMod) {
		throw new UnsupportedOperationException("TODO: translate TermVariable");
	}

	public Term translateBvArithmetic(final IProofTracker tracker, final ApplicationTerm appTerm, final Term convertedApp,
			final boolean eagerMod) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], appTerm.getParameters()[1])) {
			final Term transformed = mBvUtils.simplifyArithmeticConst(appTerm.getFunction(), appTerm.getParameters()[0],
					appTerm.getParameters()[1]);
			return mProof.trackExtractProof(appTerm, convertedApp, transformed, false, tracker, "+",
					ProofConstants.RW_EXTRACT2INT);
		}
		String integerFunctionSymbol = "";
		Annotation proof = null;
		switch (appTerm.getFunction().getName()) {
		case "bvadd": {
			integerFunctionSymbol = "+";
			proof = ProofConstants.RW_BVADD2INT;
			break;
		}
		case "bvsub": {
			integerFunctionSymbol = "-";
			proof = ProofConstants.RW_BVSUB2INT;
			break;
		}
		case "bvmul": {
			integerFunctionSymbol = "*";
			proof = ProofConstants.RW_BVMUL2INT;
			break;
		}
		default: {
			throw new UnsupportedOperationException(
					"Not an artihmetic BitVector Function: " + appTerm.getFunction().getName());
		}

		}
		Term transformed;
		if (eagerMod) {
			final BigInteger two = BigInteger.valueOf(2);
			final int width = Integer.valueOf(params[0].getSort().getIndices()[0]);
			final Term maxNumber = mTheory.rational(Rational.valueOf(two.pow(width), BigInteger.ONE),
					mTheory.getSort(SMTLIBConstants.INT));
			transformed = nat2bv(mTheory.term("mod",
					mTheory.term(integerFunctionSymbol, bv2nat(params[0], false), bv2nat(params[1], false)), maxNumber),
					params[0].getSort().getIndices());
		} else {
			transformed = nat2bv(
					mTheory.term(integerFunctionSymbol, bv2nat(params[0], eagerMod), bv2nat(params[1], eagerMod)),
					params[0].getSort().getIndices());
		}

		final Term profedTransformedBvadd = mProof.trackBvToIntProof(appTerm, convertedApp, transformed, false, tracker,
				integerFunctionSymbol, proof);
		return profedTransformedBvadd;

	}

	// nat2bv[m](2^m - bv2nat([[s]]))
	public Term translateBvNeg(final IProofTracker tracker, final ApplicationTerm appTerm, final Term convertedApp,
			final boolean eagerMod) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], null)) {
			final Term transformed = mBvUtils.simplifyNegConst(appTerm.getFunction(), appTerm.getParameters()[0]);
			return mProof.trackTODOProof(appTerm, convertedApp, transformed, false, tracker, "+",
					ProofConstants.RW_EXTRACT2INT);
		}
		final int widthInt = Integer.valueOf(appTerm.getSort().getIndices()[0]);
		final BigInteger two = BigInteger.valueOf(2);
		// 2 pow width
		final Term maxNumber = mTheory.rational(Rational.valueOf(two.pow(widthInt), BigInteger.ONE),
				mTheory.getSort(SMTLIBConstants.INT));

		// nat2bv[m](2^m - bv2nat([[s]]))
		Term transformed;
		if (eagerMod) {
			transformed = nat2bv(mTheory.term("mod", mTheory.term("-", maxNumber, bv2nat(params[0], false)), maxNumber),
					params[0].getSort().getIndices());
		} else {
			transformed =
					nat2bv(mTheory.term("-", maxNumber, bv2nat(params[0], eagerMod)), params[0].getSort().getIndices());
		}

		final Term profedTransformedBvadd = mProof.trackBvToIntProofNegNotTODO(appTerm, convertedApp, transformed, false,
				tracker, "-", ProofConstants.RW_BVMUL2INT);
		return profedTransformedBvadd;
	}

	public Term translateBvNot(final IProofTracker tracker, final ApplicationTerm appTerm, final Term convertedApp,
			final boolean eagerMod) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], null)) {
			final Term transformed = mBvUtils.simplifyNotConst(appTerm.getFunction(), appTerm.getParameters()[0]);
			return mProof.trackTODOProof(appTerm, convertedApp, transformed, false, tracker, "+",
					ProofConstants.RW_EXTRACT2INT);
		}
		final int widthInt = Integer.valueOf(appTerm.getSort().getIndices()[0]);
		final BigInteger two = BigInteger.valueOf(2);
		// 2 pow width
		final Term maxNumber = mTheory.rational(Rational.valueOf(two.pow(widthInt), BigInteger.ONE),
				mTheory.getSort(SMTLIBConstants.INT));

		final Term one = mTheory.rational(Rational.valueOf(BigInteger.ONE, BigInteger.ONE),
				mTheory.getSort(SMTLIBConstants.INT));

		final Term not = mTheory.term("-", maxNumber, mTheory.term("+", bv2nat(params[0], eagerMod), one));

		final Term transformed = nat2bv(not, params[0].getSort().getIndices());
		final Term profedTransformedBvadd = mProof.trackBvToIntProofNegNotTODO(appTerm, convertedApp, transformed, false,
				tracker, "-", ProofConstants.RW_BVMUL2INT);
		return profedTransformedBvadd;

	}

	public Term translateConcat(final IProofTracker tracker, final ApplicationTerm appTerm, final Term convertedApp,
			final boolean eagerMod) {
		final boolean mod = !eagerMod;
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], appTerm.getParameters()[1])) {
			final Term transformed = mBvUtils.simplifyConcatConst(appTerm.getFunction(), appTerm.getParameters()[0],
					appTerm.getParameters()[1]);
			return mProof.trackTODOProof(appTerm, convertedApp, transformed, false, tracker, "+",
					ProofConstants.RW_EXTRACT2INT);
		}
		final int widthInt = Integer.valueOf(appTerm.getParameters()[1].getSort().getIndices()[0]); // width of second
																									// argument
		final BigInteger two = BigInteger.valueOf(2);
		// 2 pow width
		final Term maxNumber = mTheory.rational(Rational.valueOf(two.pow(widthInt), BigInteger.ONE),
				mTheory.getSort(SMTLIBConstants.INT));
		final Term multiplication = mTheory.term("*", bv2nat(params[0], false), maxNumber);

		final Term concat = mTheory.term("+", multiplication, bv2nat(params[1], mod));
		final Term transformed = nat2bv(concat, appTerm.getSort().getIndices());
		final Term profedTransformedConcat = mProof.trackBvToIntProofConcat(appTerm, convertedApp, transformed, false,
				tracker, "+", ProofConstants.RW_CONCAT2INT);
		return profedTransformedConcat;

	}

	public Term translateBvudiv(final IProofTracker tracker, final ApplicationTerm appTerm, final Term convertedApp,
			final boolean eagerMod) {
		final boolean mod = !eagerMod;
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], appTerm.getParameters()[1])) {
			final Term transformed = mBvUtils.simplifyArithmeticConst(appTerm.getFunction(), appTerm.getParameters()[0],
					appTerm.getParameters()[1]);
			return mProof.trackTODOProof(appTerm, convertedApp, transformed, false, tracker, "+",
					ProofConstants.RW_EXTRACT2INT);
		}
		final int widthInt = Integer.valueOf(appTerm.getSort().getIndices()[0]);
		final BigInteger two = BigInteger.valueOf(2);
		// 2 pow width
		final Term maxNumberMinusOne =
				mTheory.rational(Rational.valueOf(two.pow(widthInt).subtract(BigInteger.ONE), BigInteger.ONE),
						mTheory.getSort(SMTLIBConstants.INT));

		final Term ifTerm = mTheory.term("=", bv2nat(params[1], mod),
				mTheory.rational(Rational.ZERO, mTheory.getSort(SMTLIBConstants.INT)));
		final Term thenTerm = maxNumberMinusOne;
		final Term elseTerm = mTheory.term("div", bv2nat(params[0], mod), bv2nat(params[1], mod));

		final Term transformed = nat2bv(mTheory.term("ite", ifTerm, thenTerm, elseTerm), appTerm.getSort().getIndices());

		final Term profedTransformed = mProof.trackBvudivProof(appTerm, convertedApp, transformed, false, tracker, "+",
				ProofConstants.RW_BVUDIV2INT);
		return profedTransformed;

	}

	public Term translateBvurem(final IProofTracker tracker, final ApplicationTerm appTerm, final Term convertedApp,
			final boolean eagerMod) {
		final boolean mod = !eagerMod;
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], appTerm.getParameters()[1])) {
			final Term transformed = mBvUtils.simplifyArithmeticConst(appTerm.getFunction(), appTerm.getParameters()[0],
					appTerm.getParameters()[1]);
			return mProof.trackTODOProof(appTerm, convertedApp, transformed, false, tracker, "+",
					ProofConstants.RW_EXTRACT2INT);
		}
		final Sort intSort = mTheory.getSort(SMTLIBConstants.INT);
		final Term lhs = bv2nat(params[0], mod);
		final Term rhs = bv2nat(params[1], mod);

		final Term ifTerm = mTheory.term("=", rhs, mTheory.rational(Rational.ZERO, intSort));
		final Term thenTerm = lhs;
		final Term elseTerm = mTheory.term("mod", lhs, rhs);

		final Term transformed = nat2bv(mTheory.term("ite", ifTerm, thenTerm, elseTerm), appTerm.getSort().getIndices());

		final Term profedTransformed = mProof.trackBvuremProof(appTerm, convertedApp, transformed, false, tracker, "+",
				ProofConstants.RW_BVUREM2INT);
		return profedTransformed;

	}

	public Term translateBvshl(final IProofTracker tracker, final ApplicationTerm appTerm, final Term convertedApp,
			final boolean eagerMod) {
		final boolean mod = !eagerMod;
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], appTerm.getParameters()[1])) {
			final Term transformed = mBvUtils.simplifyShiftConst(appTerm.getFunction(), appTerm.getParameters()[0],
					appTerm.getParameters()[1]);
			return mProof.trackTODOProof(appTerm, convertedApp, transformed, false, tracker, "+",
					ProofConstants.RW_EXTRACT2INT);
		}
		final Sort intSort = mTheory.getSort(SMTLIBConstants.INT);

		final Term translatedLHS = bv2nat(params[0], mod);
		final Term translatedRHS = bv2nat(params[1], mod);

		final int width = Integer.valueOf(appTerm.getSort().getIndices()[0]);
		Term iteChain = mTheory.rational(Rational.ZERO, intSort);

		// nat2bv[m](bv2nat([[s]]) * 2^(bv2nat([[t]])))

		for (int i = width - 1; i >= 0; i--) {
			if (i == 0) {
				final Term constInt = mTheory.rational(Rational.valueOf(0, 1), intSort);
				iteChain = mTheory.term("ite", mTheory.term("=", constInt, translatedRHS), translatedLHS, iteChain);
			} else {
				final Rational powResult = Rational.valueOf(i, 1);
				final Term ifTerm = mTheory.term("=", translatedRHS, mTheory.rational(powResult, intSort));
				final BigInteger pow = BigInteger.valueOf(2).pow(i);
				Term thenTerm;
				// TODO no modulo here? ist than lazy mod or is it?
				// BUG muss modulo hier rhin für eager
				thenTerm = mTheory.term("*", mTheory.rational(Rational.valueOf(pow, BigInteger.ONE), intSort),
						translatedLHS);

				if (eagerMod) {
					final Term maxNumber =
							mTheory.rational(Rational.valueOf(BigInteger.valueOf(2).pow(width), BigInteger.ONE),
									mTheory.getSort(SMTLIBConstants.INT));
					thenTerm = mTheory.term("mod", thenTerm, maxNumber);
				}
				iteChain = mTheory.term("ite", ifTerm, thenTerm, iteChain);
			}
		}
		final Term transformed = nat2bv(iteChain, appTerm.getSort().getIndices());
		final Term profedTransformed = mProof.trackBvshlProof(appTerm, convertedApp, transformed, false, tracker, "+",
				ProofConstants.RW_BVSHL2INT);
		return profedTransformed;
	}

	public Term translateBvlshr(final IProofTracker tracker, final ApplicationTerm appTerm, final Term convertedApp,
			final boolean eagerMod) {
		final boolean mod = !eagerMod;
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], appTerm.getParameters()[1])) {
			final Term transformed = mBvUtils.simplifyShiftConst(appTerm.getFunction(), appTerm.getParameters()[0],
					appTerm.getParameters()[1]);
			return mProof.trackTODOProof(appTerm, convertedApp, transformed, false, tracker, "+",
					ProofConstants.RW_EXTRACT2INT);
		}
		final Sort intSort = mTheory.getSort(SMTLIBConstants.INT);
		final int width = Integer.valueOf(appTerm.getSort().getIndices()[0]);
		// nat2bv[m](bv2nat([[s]]) div 2^(bv2nat([[t]])))
		final Term translatedLHS = bv2nat(params[0], mod);
		final Term translatedRHS = bv2nat(params[1], mod);
		Term iteChain = mTheory.rational(Rational.ZERO, intSort);

		for (int i = width - 1; i >= 0; i--) {
			if (i == 0) {
				final Term constInt = mTheory.rational(Rational.valueOf(0, 1), intSort);
				iteChain = mTheory.term("ite", mTheory.term("=", constInt, translatedRHS), translatedLHS, iteChain);
			} else {
				final Rational powResult = Rational.valueOf(i, 1);
				final Term ifTerm = mTheory.term("=", translatedRHS, mTheory.rational(powResult, intSort));
				final BigInteger pow = BigInteger.valueOf(2).pow(i);
				final Term thenTerm = mTheory.term("div", translatedLHS,
						mTheory.rational(Rational.valueOf(pow, BigInteger.ONE), intSort));
				iteChain = mTheory.term("ite", ifTerm, thenTerm, iteChain);
			}
		}

		final Term transformed = nat2bv(iteChain, appTerm.getSort().getIndices());
		final Term profedTransformed = mProof.trackBvlshrProof(appTerm, convertedApp, transformed, false, tracker, "+",
				ProofConstants.RW_BVLSHR2INT);
		return profedTransformed;

	}

	public Term translateExtract(final IProofTracker tracker, final ApplicationTerm appTerm, final Term convertedApp,
			final boolean eagerMod) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], null)) {
			return mProof.trackExtractProof(appTerm, convertedApp,
					mBvUtils.simplifySelectConst(appTerm.getFunction(), appTerm.getParameters()[0]), false, tracker,
					"+", ProofConstants.RW_EXTRACT2INT);
		}
		final Sort intSort = mTheory.getSort(SMTLIBConstants.INT);
		final Term translatedLHS = bv2nat(params[0], eagerMod);
		final BigInteger two = BigInteger.valueOf(2);
		final int lowerIndex = Integer.parseInt(appTerm.getFunction().getIndices()[1]);
		final int upperIndex = Integer.parseInt(appTerm.getFunction().getIndices()[0]);

		final Term divby = mTheory.rational(Rational.valueOf(two.pow(lowerIndex), BigInteger.ONE), intSort);

		final int extractedWidth = upperIndex - lowerIndex + 1;
		final String[] newWidth = new String[1];
		newWidth[0] = String.valueOf(extractedWidth);

		Term transformed;
		if (eagerMod) {
			final Term extractWidth = mTheory.rational(Rational.valueOf(two.pow(extractedWidth), BigInteger.ONE),
					mTheory.getSort(SMTLIBConstants.INT));
			transformed =
					nat2bv(mTheory.term("mod", mTheory.term("div", translatedLHS, divby), extractWidth), newWidth);
		} else {
			transformed = nat2bv(mTheory.term("div", translatedLHS, divby), newWidth);
		}

		final Term profedTransformed = mProof.trackExtractProof(appTerm, convertedApp, transformed, false, tracker, "+",
				ProofConstants.RW_EXTRACT2INT);
		return profedTransformed;

	}

	public Term translateRelations(final IProofTracker tracker, final ApplicationTerm appTerm, final Term convertedApp,
			final boolean eagerMod) {
		final boolean mod = !eagerMod;
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		final int width = Integer.valueOf(params[0].getSort().getIndices()[0]);

		final Term[] translatedArgs = new Term[params.length];
		for (int i = 0; i < params.length; i++) {
			translatedArgs[i] = mProof.trackTODOProof(appTerm, convertedApp, bv2nat(params[i], mod), false, tracker,
					"+", ProofConstants.RW_EXTRACT2INT);
			;
		}

		if (appTerm.getFunction().isIntern()) {
			switch (appTerm.getFunction().getName()) {
			case "distinct": {
				final Term transformed = mTheory.term("distinct", translatedArgs);
				final Term profedTransformed = mProof.trackDistinctProof(appTerm, convertedApp, transformed, false, tracker,
						"+", ProofConstants.RW_BVEQ2INT);
				return profedTransformed;
			}
			case "=": {
				final Term transformed = mTheory.term("=", translatedArgs);
				final Term profedTransformed = mProof.trackEqualProof(appTerm, convertedApp, transformed, false, tracker, "+",
						ProofConstants.RW_BVEQ2INT);
				final Term convertedEQ = mUtils.convertEq(profedTransformed);
				return convertedEQ;
			}
			case "bvult": {
				final Term transformed = mTheory.term("<", translatedArgs);
				final Term profedTransformed = mProof.trackBvultProof(appTerm, convertedApp, transformed, false, tracker, "+",
						ProofConstants.RW_BVULT2INT);
				return profedTransformed;
			}
			case "bvule": {
				final Term transformed = mTheory.term("<=", translatedArgs);
				final Term profedTransformed = mProof.trackBvuleProof(appTerm, convertedApp, transformed, false, tracker, "+",
						ProofConstants.RW_BVULE2INT);
				return profedTransformed;
			}
			case "bvugt": {
				final Term transformed = mTheory.term(">", translatedArgs);
				final Term profedTransformed = mProof.trackBvugtProof(appTerm, convertedApp, transformed, false, tracker, "+",
						ProofConstants.RW_BVUGT2INT);
				return profedTransformed;
			}
			case "bvuge": {
				final Term transformed = mTheory.term(">=", translatedArgs);
				final Term profedTransformed = mProof.trackBvugeProof(appTerm, convertedApp, transformed, false, tracker, "+",
						ProofConstants.RW_BVUGE2INT);
				return transformed;
			}
			case "bvslt": {
				final Term transformed =
						mTheory.term("<", uts(width, translatedArgs[0], mod), uts(width, translatedArgs[1], mod));
				final Term profedTransformed = mProof.trackBvsltProof(appTerm, convertedApp, transformed, false, tracker, "+",
						ProofConstants.RW_BVSLT2INT);
				return transformed;
			}
			case "bvsle": {
				final Term transformed =
						mTheory.term("<=", uts(width, translatedArgs[0], mod), uts(width, translatedArgs[1], mod));
				final Term profedTransformed = mProof.trackBvsleProof(appTerm, convertedApp, transformed, false, tracker, "+",
						ProofConstants.RW_BVSLE2INT);
				return transformed;
			}
			case "bvsgt": {
				final Term transformed = mTheory.term(">",
						mProof.trackTODOProof(appTerm, convertedApp, uts(width, translatedArgs[0], mod), false, tracker,
								"+", ProofConstants.RW_EXTRACT2INT),
						mProof.trackTODOProof(appTerm, convertedApp, uts(width, translatedArgs[1], mod), false, tracker,
								"+", ProofConstants.RW_EXTRACT2INT));
				final Term profedTransformed = mProof.trackBvsgtProof(appTerm, convertedApp, transformed, false, tracker, "+",
						ProofConstants.RW_BVSGT2INT);
				return transformed;
			}
			case "bvsge": {
				final Term transformed =
						mTheory.term(">=",
								mProof.trackTODOProof(appTerm, convertedApp, uts(width, translatedArgs[0], mod), false,
										tracker, "+", ProofConstants.RW_EXTRACT2INT),
								uts(width, translatedArgs[1], mod));
				final Term profedTransformed = mProof.trackBvsgeProof(appTerm, convertedApp, transformed, false, tracker, "+",
						ProofConstants.RW_BVSGE2INT);
				return transformed;
			}
			}
		}
		throw new UnsupportedOperationException("unexpected relation");
	}

	// unsigned to signed for relations
	private final Term uts(final int width, Term bv2natparam, final boolean eagerMod) {
		// 2 * (x mod 2^(k - 1) ) - x
		// 2 * nat2bv_{k - 1}(bv2nat(param)) - x)
		final Sort intSort = mTheory.getSort(SMTLIBConstants.INT);
		// String[] newWidth = new String[1];
		// newWidth[0] = String.valueOf(width - 1);

		// Is now bv2nat(nat2bv_k-1(bv2nat(param)))
		// Egaer this should become (param mod 2^k−1)
		// Lazy this should become ((param mod 2^k) mod 2^k−1)
		// And bv2nat(param) should eager become param
		// And Lazy bv2nat(param) become (param mod 2^k)
		final BigInteger twoBigInt = BigInteger.valueOf(2);
		final int newwidth = width - 1;
		final Term newMaxNumber = mTheory.rational(Rational.valueOf(twoBigInt.pow(newwidth), BigInteger.ONE),
				mTheory.getSort(SMTLIBConstants.INT));
		final Term maxNumber = mTheory.rational(Rational.valueOf(twoBigInt.pow(width), BigInteger.ONE),
				mTheory.getSort(SMTLIBConstants.INT));
		bv2natparam = mTheory.term("mod", bv2natparam, maxNumber);
		final Term modulo = mTheory.term("mod", bv2natparam, newMaxNumber);
		final Term two = mTheory.rational(Rational.TWO, intSort);
		return mTheory.term("-", mTheory.term("*", two, modulo), bv2natparam);
	}

}
