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
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofTracker;

public class BvToIntUtils {

	private final Theory mTheory;
	private final LogicSimplifier mUtils;
	private final BvUtils mBvUtils;
	private final static String BITVEC_CONST_PATTERN = "bv\\d+";

	public BvToIntUtils(final Theory theory, final LogicSimplifier utils, BvUtils bvutils) {
		mTheory = theory;
		mUtils = utils;
		mBvUtils = bvutils;
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
	public Term bv2nat(Term param, boolean eagerMod) {
		assert param.getSort().isBitVecSort();
		// width of the first argument

		final BigInteger two = BigInteger.valueOf(2);
		// maximal representable number by a bit-vector of width "width"

		if (mBvUtils.isConstRelation(param, null)) {
			if (param instanceof ConstantTerm) {
				return translateConstant(((ConstantTerm) param).getValue());
			} else {
				BigInteger value = new BigInteger(((ApplicationTerm) param).getFunction().getName().substring(2));
				return translateConstant(value);
			}

		}
		if (param instanceof ApplicationTerm) { // TODO doesnt work somehow, reason probably clausifier
			ApplicationTerm apParam = (ApplicationTerm) param;
			// Problem: bv2nat(nat2bv(t)) // can only be removed if value fits in bv width
			if (apParam.getFunction().getName().equals("nat2bv")) {
				final int width = Integer.valueOf(apParam.getSort().getIndices()[0]);
				final Term maxNumber = mTheory.rational(Rational.valueOf(two.pow(width), BigInteger.ONE),
						mTheory.getSort(SMTLIBConstants.INT));
				return mTheory.term("mod", apParam.getParameters()[0], maxNumber); // !!!CAnnot be eliminated here,
																					// needs a modulo
			}
		}

		// TODO optimize bv2nat bv2nat
		return mTheory.term("bv2nat", param);
	}

	/*
	 * TODO RangeBased "nat2bv""bv2nat" -> mod,?
	 */
	public Term nat2bv(Term param, String[] width, boolean eagerMod) {
		assert param.getSort().isNumericSort();
		// TODO case switch for simplifications
		// width of the first argument
		final int widthInt = Integer.valueOf(width[0]);
		final BigInteger two = BigInteger.valueOf(2);
		// maximal representable number by a bit-vector of width "width"
		final Term maxNumber = mTheory.rational(Rational.valueOf(two.pow(widthInt), BigInteger.ONE),
				mTheory.getSort(SMTLIBConstants.INT));
		// TODO optimize nat2bv nat2bv
		if (param instanceof ConstantTerm) {
			return translateConstantBack((Rational) ((ConstantTerm) param).getValue(), width);
		}
		if (param instanceof ApplicationTerm) {
			ApplicationTerm apParam = (ApplicationTerm) param;
			if (apParam.getFunction().getName().equals("bv2nat")) {
				if (width.equals(apParam.getParameters()[0].getSort().getIndices())) {
					return apParam.getParameters()[0];
				}

			}
		}
		return mTheory.term("nat2bv", width, null, param);
	}

	/*
	 * This methods creates the rewrite proofs for the bv to int translations. The pattern of this method should be
	 * applicable for all translation rules.
	 * 
	 * TODO return void or ergebnissimplify?
	 * 
	 * TODO make mor modular, what if only one parameter
	 */

	public Term trackBvToIntProof(ApplicationTerm original, ApplicationTerm convertedApp, Term translationResult,
			boolean eagerMod, IProofTracker tracker, String integerFsym, Annotation functionAnnotation) {
		Term[] params = original.getParameters();
		Term originalRW =
				tracker.buildRewrite(tracker.getProvedTerm(convertedApp), translationResult, functionAnnotation);
		Term functionRW = tracker.congruence(
				tracker.reflexivity(mTheory.term(integerFsym, mTheory.term("bv2nat", params[0]),
						mTheory.term("bv2nat", params[1]))),
				new Term[] { trackBv2NatProof(mTheory.term("bv2nat", params[0]), eagerMod, tracker),
						trackBv2NatProof(mTheory.term("bv2nat", params[1]), eagerMod, tracker) });

		// TODO is proof for nat2bv() this missing?
		// tracker.buildRewrite(mTheory.term("nat2bv", functionRW), nat2bv(functionRW,eagerMod),
		// ProofConstants.RW_NAT2BV );

		Term ergebnissimplify = tracker.congruence(originalRW, new Term[] { functionRW });
		Term proofed = tracker.transitivity(convertedApp, ergebnissimplify);
		return proofed;
	}

	private Term trackBvToIntProofNegNotTODO(ApplicationTerm appTerm, ApplicationTerm convertedApp, Term transformed,
			boolean b, IProofTracker tracker, String string, Annotation annotation) {
		// TODO Auto-generated method stub
		return transformed;
	}

	public Term trackBv2NatProof(Term bv2nat, boolean eagerMod, IProofTracker tracker) {
		assert bv2nat instanceof ApplicationTerm;
		// TODO
		return tracker.buildRewrite(bv2nat, bv2nat(((ApplicationTerm) bv2nat).getParameters()[0], eagerMod),
				ProofConstants.RW_BV2NAT);
	}

	private Term trackBvToIntProofConcat(ApplicationTerm appTerm, ApplicationTerm convertedApp, Term transformed,
			boolean b, IProofTracker tracker, String string, String rwConcat2int) {
		// TODO Auto-generated method stub
		return transformed;
	}

	private Term trackProofTodo(ApplicationTerm appTerm, ApplicationTerm convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, String rwConcat2int) {
		// TODO Auto-generated method stub
		return transformed;
	}

	/*
	 * transforms a bitvector constant c to nat2bv(c')
	 */
	public Term translateBvConstant(final FunctionSymbol fsym, Term convertedApp, boolean eagerMod) {
		if (convertedApp.getSort().isBitVecSort()) {
			BigInteger value = new BigInteger(fsym.getName().substring(2));
			return nat2bv(translateConstant(value), convertedApp.getSort().getIndices(), eagerMod);
		} else {
			throw new UnsupportedOperationException("Can't convert bv constant: " + fsym.getName());
		}
	}

	/*
	 * transforms a bitvector constant c to nat2bv(c')
	 */
	public Term translateBvConstantTerm(ConstantTerm term, boolean eagerMod) {
		if (term.getSort().isBitVecSort()) {
			return nat2bv(translateConstant(term.getValue()), term.getSort().getIndices(), eagerMod);
		} else {
			throw new UnsupportedOperationException("Can't convert bv constant: " + term);
		}
	}

	/*
	 * Gets as Input the value of a bit-vec const and returns an integer constant
	 */
	private Term translateConstant(Object value) {
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

	private Term translateConstantBack(Rational value, String[] width ) {
	
		Rational valueInRange = Rational.valueOf(value.numerator().mod(BigInteger.TWO.pow(Integer.valueOf(width[0]))),
				BigInteger.ONE);
			return mTheory.term("bv" + valueInRange, width, null);
		
		
	}

	public Term translateTermVariable(TermVariable term, boolean mEagerMod) {
		throw new UnsupportedOperationException("TODO: translate TermVariable");
	}

	public Term translateBvArithmetic(IProofTracker tracker, final ApplicationTerm appTerm, Term convertedApp,
			boolean eagerMod) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], appTerm.getParameters()[1])) {
			return mBvUtils.simplifyArithmeticConst(appTerm.getFunction(), appTerm.getParameters()[0],
					appTerm.getParameters()[1]);
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
		Term transformed =
				nat2bv(mTheory.term(integerFunctionSymbol, bv2nat(params[0], eagerMod), bv2nat(params[1], eagerMod)),
						params[0].getSort().getIndices(), eagerMod);
		Term profedTransformedBvadd = trackBvToIntProof(appTerm, (ApplicationTerm) convertedApp, transformed, false,
				tracker, integerFunctionSymbol, proof);
		return profedTransformedBvadd;

	}

	// nat2bv[m](2^m - bv2nat([[s]]))
	public Term translateBvNeg(IProofTracker tracker, final ApplicationTerm appTerm, Term convertedApp,
			boolean eagerMod) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], null)) {
			return mBvUtils.simplifyNegConst(appTerm.getFunction(), appTerm.getParameters()[0]);
		}
		final int widthInt = Integer.valueOf(appTerm.getSort().getIndices()[0]);
		final BigInteger two = BigInteger.valueOf(2);
		// 2 pow width
		final Term maxNumber = mTheory.rational(Rational.valueOf(two.pow(widthInt), BigInteger.ONE),
				mTheory.getSort(SMTLIBConstants.INT));

		// nat2bv[m](2^m - bv2nat([[s]]))
		Term transformed = nat2bv(mTheory.term("-", maxNumber, bv2nat(params[0], eagerMod)),
				params[0].getSort().getIndices(), eagerMod);
		Term profedTransformedBvadd = trackBvToIntProofNegNotTODO(appTerm, (ApplicationTerm) convertedApp, transformed,
				false, tracker, "-", ProofConstants.RW_BVMUL2INT);
		return profedTransformedBvadd;
	}

	public Term translateBvNot(IProofTracker tracker, final ApplicationTerm appTerm, Term convertedApp,
			boolean eagerMod) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], null)) {
			return mBvUtils.simplifyNotConst(appTerm.getFunction(), appTerm.getParameters()[0]);
		}
		final int widthInt = Integer.valueOf(appTerm.getSort().getIndices()[0]);
		final BigInteger two = BigInteger.valueOf(2);
		// 2 pow width
		final Term maxNumber = mTheory.rational(Rational.valueOf(two.pow(widthInt), BigInteger.ONE),
				mTheory.getSort(SMTLIBConstants.INT));

		Term one = mTheory.rational(Rational.valueOf(BigInteger.ONE, BigInteger.ONE),
				mTheory.getSort(SMTLIBConstants.INT));

		final Term not = mTheory.term("-", maxNumber, mTheory.term("+", bv2nat(params[0], eagerMod), one));

		Term transformed = nat2bv(not, params[0].getSort().getIndices(), eagerMod);
		Term profedTransformedBvadd = trackBvToIntProofNegNotTODO(appTerm, (ApplicationTerm) convertedApp, transformed,
				false, tracker, "-", ProofConstants.RW_BVMUL2INT);
		return profedTransformedBvadd;

	}

	public Term translateConcat(IProofTracker tracker, final ApplicationTerm appTerm, Term convertedApp,
			boolean eagerMod) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], appTerm.getParameters()[1])) {
			return mBvUtils.simplifyConcatConst(appTerm.getFunction(), appTerm.getParameters()[0],
					appTerm.getParameters()[1]);
		}
		final int widthInt = Integer.valueOf(appTerm.getParameters()[1].getSort().getIndices()[0]); // width of second
																									// argument
		final BigInteger two = BigInteger.valueOf(2);
		// 2 pow width
		final Term maxNumber = mTheory.rational(Rational.valueOf(two.pow(widthInt), BigInteger.ONE),
				mTheory.getSort(SMTLIBConstants.INT));
		final Term multiplication = mTheory.term("*", bv2nat(params[0], eagerMod), maxNumber);

		Term concat = mTheory.term("+", multiplication, bv2nat(params[1], eagerMod));
		Term transformed = nat2bv(concat, appTerm.getSort().getIndices(), eagerMod);
		Term profedTransformedConcat = trackBvToIntProofConcat(appTerm, (ApplicationTerm) convertedApp, transformed,
				false, tracker, "+", ProofConstants.RW_CONCAT2INT);
		return profedTransformedConcat;

	}

	public Term translateBvudiv(IProofTracker tracker, final ApplicationTerm appTerm, Term convertedApp,
			boolean eagerMod) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], appTerm.getParameters()[1])) {
			return mBvUtils.simplifyArithmeticConst(appTerm.getFunction(), appTerm.getParameters()[0],
					appTerm.getParameters()[1]);
		}
		final int widthInt = Integer.valueOf(appTerm.getSort().getIndices()[0]);
		final BigInteger two = BigInteger.valueOf(2);
		// 2 pow width
		final Term maxNumberMinusOne =
				mTheory.rational(Rational.valueOf(two.pow(widthInt).subtract(BigInteger.ONE), BigInteger.ONE),
						mTheory.getSort(SMTLIBConstants.INT));

		final Term ifTerm = mTheory.term("=", bv2nat(params[1], eagerMod),
				mTheory.rational(Rational.ZERO, mTheory.getSort(SMTLIBConstants.INT)));
		final Term thenTerm = maxNumberMinusOne;
		final Term elseTerm = mTheory.term("div", bv2nat(params[0], eagerMod), bv2nat(params[1], eagerMod));

		Term transformed =
				nat2bv(mTheory.term("ite", ifTerm, thenTerm, elseTerm), appTerm.getSort().getIndices(), eagerMod);

		Term profedTransformed = trackProofTodo(appTerm, (ApplicationTerm) convertedApp, transformed, false, tracker,
				"+", ProofConstants.RW_BVUDIV2INT);
		return profedTransformed;

	}

	public Term translateBvurem(IProofTracker tracker, final ApplicationTerm appTerm, Term convertedApp,
			boolean eagerMod) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], appTerm.getParameters()[1])) {
			return mBvUtils.simplifyArithmeticConst(appTerm.getFunction(), appTerm.getParameters()[0],
					appTerm.getParameters()[1]);
		}
		final Sort intSort = mTheory.getSort(SMTLIBConstants.INT);
		Term lhs = bv2nat(params[0], eagerMod);
		Term rhs = bv2nat(params[1], eagerMod);

		final Term ifTerm = mTheory.term("=", rhs, mTheory.rational(Rational.ZERO, intSort));
		final Term thenTerm = lhs;
		final Term elseTerm = mTheory.term("mod", lhs, rhs);

		Term transformed =
				nat2bv(mTheory.term("ite", ifTerm, thenTerm, elseTerm), appTerm.getSort().getIndices(), eagerMod);

		Term profedTransformed = trackProofTodo(appTerm, (ApplicationTerm) convertedApp, transformed, false, tracker,
				"+", ProofConstants.RW_BVUREM2INT);
		return profedTransformed;

	}

	public Term translateBvshl(IProofTracker tracker, final ApplicationTerm appTerm, Term convertedApp,
			boolean eagerMod) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], appTerm.getParameters()[1])) {
			return mBvUtils.simplifyShiftConst(appTerm.getFunction(), appTerm.getParameters()[0],
					appTerm.getParameters()[1]);
		}
		final Sort intSort = mTheory.getSort(SMTLIBConstants.INT);

		Term translatedLHS = bv2nat(params[0], eagerMod);
		Term translatedRHS = bv2nat(params[1], eagerMod);

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
				final Term thenTerm;
				// TODO no modulo here? ist than lazy mod or is it?
				thenTerm = mTheory.term("*", mTheory.rational(Rational.valueOf(pow, BigInteger.ONE), intSort),
						translatedLHS);

				iteChain = mTheory.term("ite", ifTerm, thenTerm, iteChain);
			}
		}
		Term transformed = nat2bv(iteChain, appTerm.getSort().getIndices(), eagerMod);
		Term profedTransformed = trackProofTodo(appTerm, (ApplicationTerm) convertedApp, transformed, false, tracker,
				"+", ProofConstants.RW_BVSHL2INT);
		return profedTransformed;
	}

	public Term translateBvlshr(IProofTracker tracker, final ApplicationTerm appTerm, Term convertedApp,
			boolean eagerMod) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], appTerm.getParameters()[1])) {
			return mBvUtils.simplifyShiftConst(appTerm.getFunction(), appTerm.getParameters()[0],
					appTerm.getParameters()[1]);
		}
		final Sort intSort = mTheory.getSort(SMTLIBConstants.INT);
		final int width = Integer.valueOf(appTerm.getSort().getIndices()[0]);
		// nat2bv[m](bv2nat([[s]]) div 2^(bv2nat([[t]])))
		Term translatedLHS = bv2nat(params[0], eagerMod);
		Term translatedRHS = bv2nat(params[1], eagerMod);
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

		Term transformed = nat2bv(iteChain, appTerm.getSort().getIndices(), eagerMod);
		Term profedTransformed = trackProofTodo(appTerm, (ApplicationTerm) convertedApp, transformed, false, tracker,
				"+", ProofConstants.RW_BVLSHR2INT);
		return profedTransformed;

	}

	public Term translateExtract(IProofTracker tracker, final ApplicationTerm appTerm, Term convertedApp,
			boolean eagerMod) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		if (mBvUtils.isConstRelation(appTerm.getParameters()[0], null)) {
			return mBvUtils.simplifySelectConst(appTerm.getFunction(), appTerm.getParameters()[0]);
		}
		final Sort intSort = mTheory.getSort(SMTLIBConstants.INT);
		Term translatedLHS = bv2nat(params[0], eagerMod);
		final BigInteger two = BigInteger.valueOf(2);
		final int lowerIndex = Integer.parseInt(appTerm.getFunction().getIndices()[1]);
		final int upperIndex = Integer.parseInt(appTerm.getFunction().getIndices()[0]);

		final Term divby = mTheory.rational(Rational.valueOf(two.pow(lowerIndex), BigInteger.ONE), intSort);

		int extractedWidth = upperIndex - lowerIndex + 1;
		String[] newWidth = new String[1];
		newWidth[0] = String.valueOf(extractedWidth);
		Term transformed = nat2bv(mTheory.term("div", translatedLHS, divby), newWidth, eagerMod);
		Term profedTransformed = trackProofTodo(appTerm, (ApplicationTerm) convertedApp, transformed, false, tracker,
				"+", ProofConstants.RW_EXTRACT2INT);
		return profedTransformed;

	}

	public Term translateRelations(IProofTracker tracker, final ApplicationTerm appTerm, Term convertedApp,
			boolean eagerMod) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		final int width = Integer.valueOf(params[0].getSort().getIndices()[0]);

		Term[] translatedArgs = new Term[params.length];
		for (int i = 0; i < params.length; i++) {
			translatedArgs[i] = bv2nat(params[i], eagerMod);
		}

		if (appTerm.getFunction().isIntern()) {
			switch (appTerm.getFunction().getName()) {
			case "distinct": {
				Term transformed = mTheory.term("distinct", translatedArgs);
				Term profedTransformed = trackProofTodo(appTerm, (ApplicationTerm) convertedApp, transformed, false,
						tracker, "+", ProofConstants.RW_BVEQ2INT);
				return profedTransformed;
			}
			case "=": {
				Term transformed = mTheory.term("=", translatedArgs);
				Term profedTransformed = trackProofTodo(appTerm, (ApplicationTerm) convertedApp, transformed, false,
						tracker, "+", ProofConstants.RW_BVEQ2INT);
				Term convertedEQ = mUtils.convertEq(profedTransformed);
				return convertedEQ;
			}
			case "bvult": {
				Term transformed = mTheory.term("<", translatedArgs);
				Term profedTransformed = trackProofTodo(appTerm, (ApplicationTerm) convertedApp, transformed, false,
						tracker, "+", ProofConstants.RW_BVULT2INT);
				return profedTransformed;
			}
			case "bvule": {
				Term transformed = mTheory.term("<=", translatedArgs);
				Term profedTransformed = trackProofTodo(appTerm, (ApplicationTerm) convertedApp, transformed, false,
						tracker, "+", ProofConstants.RW_BVULE2INT);
				return profedTransformed;
			}
			case "bvugt": {
				Term transformed = mTheory.term(">", translatedArgs);
				Term profedTransformed = trackProofTodo(appTerm, (ApplicationTerm) convertedApp, transformed, false,
						tracker, "+", ProofConstants.RW_BVUGT2INT);
				return profedTransformed;
			}
			case "bvuge": {
				Term transformed = mTheory.term(">=", translatedArgs);
				Term profedTransformed = trackProofTodo(appTerm, (ApplicationTerm) convertedApp, transformed, false,
						tracker, "+", ProofConstants.RW_BVUGE2INT);
				return profedTransformed;
			}
			case "bvslt": {
				Term transformed = mTheory.term("<", uts(width, translatedArgs[0], eagerMod),
						uts(width, translatedArgs[1], eagerMod));
				Term profedTransformed = trackProofTodo(appTerm, (ApplicationTerm) convertedApp, transformed, false,
						tracker, "+", ProofConstants.RW_BVSLT2INT);
				return profedTransformed;
			}
			case "bvsle": {
				Term transformed = mTheory.term("<=", uts(width, translatedArgs[0], eagerMod),
						uts(width, translatedArgs[1], eagerMod));
				Term profedTransformed = trackProofTodo(appTerm, (ApplicationTerm) convertedApp, transformed, false,
						tracker, "+", ProofConstants.RW_BVSLE2INT);
				return profedTransformed;
			}
			case "bvsgt": {
				Term transformed = mTheory.term(">", uts(width, translatedArgs[0], eagerMod),
						uts(width, translatedArgs[1], eagerMod));
				Term profedTransformed = trackProofTodo(appTerm, (ApplicationTerm) convertedApp, transformed, false,
						tracker, "+", ProofConstants.RW_BVSGT2INT);
				return profedTransformed;
			}
			case "bvsge": {
				Term transformed = mTheory.term(">=", uts(width, translatedArgs[0], eagerMod),
						uts(width, translatedArgs[1], eagerMod));
				Term profedTransformed = trackProofTodo(appTerm, (ApplicationTerm) convertedApp, transformed, false,
						tracker, "+", ProofConstants.RW_BVSGE2INT);
				return profedTransformed;
			}
			}
		}
		throw new UnsupportedOperationException("unexpected relation");
	}

	// unsigned to signed for relations
	private final Term uts(final int width, final Term bv2natparam, final boolean eagerMod) {
		// 2 * (x mod 2^(k - 1) ) - x
		// 2 * nat2bv_{k - 1}(bv2nat(param)) - x)
		final Sort intSort = mTheory.getSort(SMTLIBConstants.INT);
		String[] newWidth = new String[1];
		newWidth[0] = String.valueOf(width - 1);

		// Is now bv2nat(nat2bv_k-1(bv2nat(param)))
		// Egaer this should become (param mod 2^k−1)
		// Lazy this should become ((param mod 2^k) mod 2^k−1)
		// And bv2nat(param) should eager become param
		// And Lazy bv2nat(param) become (param mod 2^k)
		final Term modulo = bv2nat(nat2bv(bv2natparam, newWidth, eagerMod), eagerMod);
		Term two = mTheory.rational(Rational.TWO, intSort);
		return mTheory.term("-", mTheory.term("*", two, modulo), bv2natparam);

	}

}
