package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.LogicSimplifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;

public class BvToIntProofTracker {
	private final Theory mTheory;
	private final LogicSimplifier mUtils;
	private final BvUtils mBvUtils;
	private final BvToIntUtils mBvToIntUtils;
	private final static String BITVEC_CONST_PATTERN = "bv\\d+";
	
	public BvToIntProofTracker(final Theory theory, final LogicSimplifier utils, BvUtils bvutils, BvToIntUtils bvtointutils) {
		mTheory = theory;
		mUtils = utils;
		mBvUtils = bvutils;
		mBvToIntUtils = bvtointutils;
	}
	
	
	
	/*
	 * This methods creates the rewrite proofs for the bv to int translations. The pattern of this method should be
	 * applicable for all translation rules.
	 * 
	 * TODO return void or ergebnissimplify?
	 * 
	 * TODO make mor modular, what if only one parameter
	 */
	public Term trackBvToIntProof(ApplicationTerm original, Term convertedApp, Term translationResult,
			boolean eagerMod, IProofTracker tracker, String integerFsym, Annotation functionAnnotation) {
//		Term[] params = original.getParameters();
//		Term originalRW =
//				tracker.buildRewrite(tracker.getProvedTerm(convertedApp), translationResult, functionAnnotation);
//		Term functionRW = tracker.congruence(
//				tracker.reflexivity(mTheory.term(integerFsym, mTheory.term("bv2nat", params[0]),
//						mTheory.term("bv2nat", params[1]))),
//				new Term[] { trackBv2NatProof(mTheory.term("bv2nat", params[0]), eagerMod, tracker),
//						trackBv2NatProof(mTheory.term("bv2nat", params[1]), eagerMod, tracker) });
//
//		// TODO is proof for nat2bv() this missing?
//		// tracker.buildRewrite(mTheory.term("nat2bv", functionRW), nat2bv(functionRW,eagerMod),
//		// ProofConstants.RW_NAT2BV );
//
//		Term ergebnissimplify = tracker.congruence(originalRW, new Term[] { functionRW });
//		Term proofed = tracker.transitivity(convertedApp, ergebnissimplify);
//		return proofed;
		return tracker.reflexivity(translationResult);
	}

	public Term trackBvToIntProofNegNotTODO(ApplicationTerm appTerm, Term convertedApp, Term transformed,
			boolean b, IProofTracker tracker, String string, Annotation annotation) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}

	public Term trackBv2NatProof(Term bv2nat, boolean eagerMod, IProofTracker tracker) {
		assert bv2nat instanceof ApplicationTerm;
		// TODO
		return tracker.reflexivity(bv2nat);
	}

	
	public Term trackBvToIntProofConcat(ApplicationTerm appTerm, Term convertedApp, Term transformed,
			boolean b, IProofTracker tracker, String string, Annotation rwConcat2int) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}



	public Term trackBvudivProof(ApplicationTerm appTerm, Term convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, Annotation rwBvudiv2int) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}



	public Term trackBvuremProof(ApplicationTerm appTerm, Term convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, Annotation rwBvurem2int) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}



	public Term trackBvshlProof(ApplicationTerm appTerm, Term convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, Annotation rwBvshl2int) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}



	public Term trackExtractProof(ApplicationTerm appTerm, Term convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, Annotation rwExtract2int) {
		
		return tracker.reflexivity(transformed);
	}



	public Term trackBvlshrProof(ApplicationTerm appTerm, Term convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, Annotation rwBvlshr2int) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}
	public Term trackDistinctProof(ApplicationTerm appTerm, Term convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, Annotation rwBveq2int) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}

	public Term trackEqualProof(ApplicationTerm appTerm, Term convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, Annotation rwBveq2int) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}

	public Term trackBvultProof(ApplicationTerm appTerm, Term convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, Annotation rwBvult2int) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}

	public Term trackBvuleProof(ApplicationTerm appTerm, Term convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, Annotation rwBvule2int) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}

	public Term trackBvugtProof(ApplicationTerm appTerm, Term convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, Annotation rwBvugt2int) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}

	public Term trackBvugeProof(ApplicationTerm appTerm, Term convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, Annotation rwBvuge2int) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}

	public Term trackBvsltProof(ApplicationTerm appTerm, Term convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, Annotation rwBvslt2int) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}

	public Term trackBvsleProof(ApplicationTerm appTerm, Term convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, Annotation rwBvsle2int) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}

	public Term trackBvsgtProof(ApplicationTerm appTerm, Term convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, Annotation rwBvsgt2int) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}

	public Term trackBvsgeProof(ApplicationTerm appTerm, Term convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, Annotation rwBvsge2int) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}
	public Term trackTODOProof(ApplicationTerm appTerm, Term convertedApp, Term transformed, boolean b,
			IProofTracker tracker, String string, Annotation rwBvsge2int) {
		// TODO Auto-generated method stub
		return tracker.reflexivity(transformed);
	}
}