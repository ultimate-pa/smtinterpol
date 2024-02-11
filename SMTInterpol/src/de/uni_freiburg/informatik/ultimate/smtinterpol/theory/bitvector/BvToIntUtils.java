package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.LogicSimplifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofTracker;

public class BvToIntUtils {
	
	private final Theory mTheory;
	private final LogicSimplifier mUtils;

	public BvToIntUtils(final Theory theory, final LogicSimplifier utils) {
		mTheory = theory;
		mUtils = utils;
	}
	
	
	
	/*
	 * Deals with the uninterpreted function symbol bv2nat.
	 * Call this instead of theory.term("bv2nat", param);
	 * Does local simplifications, without using pushTerm to go throu the term again.
	 * Replaces bv2nat by a modulo in most cases
	 * 
	 * At the end bv2nat should only be around uninterpreted functions (constants variables, selects, ...)
	 * 
	 * TODO
	 * 
	 * Case Switch, param is nat2bv (return param of nat2bv), param is constant, 
	 * 
	 */
	public Term bv2nat(Term param, boolean eagerMod) {
		
		// width of the first argument
		final int width = Integer.valueOf(param.getSort().getIndices()[0]);	
		final BigInteger two = BigInteger.valueOf(2);
		// maximal representable number by a bit-vector of width "width"
		final Term maxNumber = mTheory.rational(Rational.valueOf(two.pow(width), BigInteger.ONE), mTheory.getSort(SMTLIBConstants.INT));
	
		
		//TODO case switch for simplifications
		
		return  mTheory.term("bv2nat", param);
	}
	
	
	/*
	 * TODO RangeBased "nat2bv""bv2nat" -> mod,
	 */
	public Term nat2bv(Term param, String[] width,  boolean eagerMod)  {
		
		//TODO case switch for simplifications
		
		return  mTheory.term("nat2bv", width, null, param);
	}
	
	
	/* 
	 * This methods creates the rewrite proofs for the bv to int translations.
	 * The pattern of this method should be applicable for all translation rules.
	 * 
	 * TODO return void or ergebnissimplify?
	 */
	
	public void trackBvToIntProof(ApplicationTerm original, ApplicationTerm convertedApp, Term translationResult, 
			boolean eagerMod, IProofTracker tracker, String integerFsym, Annotation functionAnnotation){		
		Term[] params = original.getParameters();		
		Term originalRW = tracker.buildRewrite(tracker.getProvedTerm(convertedApp), translationResult, functionAnnotation);		
		Term functionRW = tracker.congruence(								
						tracker.reflexivity(
								mTheory.term(integerFsym, mTheory.term("bv2nat", params[0]), mTheory.term("bv2nat", params[1]))),
								new Term[] {
										trackBv2NatProof(mTheory.term("bv2nat", params[0]),eagerMod, tracker),
										trackBv2NatProof(mTheory.term("bv2nat", params[1]),eagerMod, tracker)}
				);
		
		//TODO is proof for nat2bv() this missing?
		//tracker.buildRewrite(mTheory.term("nat2bv", functionRW), nat2bv(functionRW,eagerMod), ProofConstants.RW_NAT2BV );
				
		Term ergebnissimplify = tracker.congruence(originalRW, new Term[] {functionRW} );	
		tracker.transitivity(convertedApp, ergebnissimplify);
	}
	
	public Term trackBv2NatProof(Term bv2nat, boolean eagerMod, IProofTracker tracker ){
		assert bv2nat instanceof ApplicationTerm;		
		return tracker.buildRewrite(bv2nat, bv2nat(((ApplicationTerm) bv2nat).getParameters()[0],eagerMod), ProofConstants.RW_BV2NAT );
	}


	/*
	 * transforms a bitvector constant c to nat2bv(c')
	 */
	public Term translateBvConstant(final FunctionSymbol fsym, Term convertedApp, boolean eagerMod) {
			if (convertedApp.getSort().isBitVecSort()) {
				BigInteger value = new BigInteger(fsym.getName().substring(2));
				return nat2bv(mTheory.rational(Rational.valueOf(value, BigInteger.ONE), 
						mTheory.getSort(SMTLIBConstants.INT)), convertedApp.getSort().getIndices(), eagerMod);
				
			} else{
				throw new UnsupportedOperationException("Can't convert bv constant: " + fsym.getName());
			}
			
		}
	
}


	
	
	
	
			
	
	
