//package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;
//
//import java.util.ArrayList;
//import java.util.HashMap;
//import java.util.HashSet;
//
//import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
//import de.uni_freiburg.informatik.ultimate.logic.Term;
//
///**
// * Represents an almost-all atom.
// * TODO: think of something more efficient for the signature handling
// * @author Alexander Nutz
// */
//public class EprAlmostAllAtom extends EprAtom {
//
//	public final EprPredicate eprPredicate;
//	
//	/**
//	 * Maps the nth argument to the indices of all arguments that have the same variable in the signature.
//	 * (for example (P x y x) will yield the signature [{1,3}, {2}, {1,3}])
//	 * TODO: find something more efficient
//	 */
////	public final ArrayList<HashSet<Integer>> signature;
//	public final AAAtomSignature signature;
//	
//
////	public EprAlmostAllAtom(ApplicationTerm term, int hash, int assertionstacklevel, EprPredicate eprPred, Term[] argumentsForPattern) {
////		//TODO: make sure hash matches equals given below
////		super(term, hash, assertionstacklevel);
////		eprPredicate = eprPred;
////
////		signature = computeSignature(eprPred.arity, argumentsForPattern);
////	}
//
//
//
//	
//	public EprAlmostAllAtom(Term term, int hash, int assertionStackLevel, EprPredicate eprPred,
//			AAAtomSignature sig) {
//		//TODO: make sure hash matches equals given below
//		super(term, hash, assertionStackLevel);
//		eprPredicate = eprPred;
//
//		signature = sig;
//
//		this.isQuantified = false;
//	}
//
//
//
//
////	/**
////	 * 
////	 * @param other
////	 * @return true iff, by our assumed semantics, this implies other
////	 */
////	public boolean signatureImplies(EprAlmostAllAtom other) {
////		assert other.eprPredicate.arity == this.eprPredicate.arity;
////
////		//check:
////		// at every point, the signatures partition must be subset of other's signature's partition..
////		boolean result = true;
////		for (int i = 0; i < this.eprPredicate.arity; i++) 
////			result = result && other.signature.get(i).containsAll(this.signature.get(i));
////		
////		return result;
////	}
//
//
//	@Override
//	public boolean equals(Object obj) {
//		if (!(obj instanceof EprAlmostAllAtom))
//			return false;
//		
//		EprAlmostAllAtom eaaa = (EprAlmostAllAtom) obj;
//
//		return eprPredicate.equals(eaaa.eprPredicate) && signature.equals(eaaa.signature);
//	}
//
//
//	
//
////	public EprPredicate getEprPredicate() {
////		return mEprPredicate;
////	}
//}
