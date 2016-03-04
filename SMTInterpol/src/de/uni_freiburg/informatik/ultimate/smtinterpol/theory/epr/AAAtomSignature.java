package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.HashSet;

public class AAAtomSignature {

	/**
	 * Maps the nth argument to the indices of all arguments that have the same variable in the signature.
	 * (for example (P x y x) will yield the signature [{1,3}, {2}, {1,3}])
	 * TODO: find something more efficient
	 */
	private final ArrayList<HashSet<Integer>> mRepetitionSignature;

	private final ArrayList<HashSet<Integer>> mExceptReflSignature;
	
	private final boolean mNegated;
	
	public AAAtomSignature(ArrayList<HashSet<Integer>> repSig, ArrayList<HashSet<Integer>> exceptReflSig, boolean negated) {
		mRepetitionSignature = repSig;
		mExceptReflSignature = exceptReflSig;
		mNegated = negated;
	}
	
	/**
	 * 
	 * @param other
	 * @return true iff, by our assumed semantics, this implies other
	 */
	public boolean implies(AAAtomSignature other) {
		assert this.mRepetitionSignature.size() == other.mRepetitionSignature.size();
		
		if (this.mNegated == other.mNegated) {
			
			
			
			
			
			//check:
			// at every point, the signatures partition must be subset of other's signature's partition..
			for (int i = 0; i < this.mRepetitionSignature.size(); i++) 
				if (!other.mRepetitionSignature.get(i).containsAll(this.mRepetitionSignature.get(i)))
					return false;

			return true;

			
		} else {
			
		}


		return false;
	}

	@Override
	public boolean equals(Object arg0) {
		if (!(arg0 instanceof AAAtomSignature)) return false;

		AAAtomSignature other = (AAAtomSignature) arg0;
		
		if (this.mNegated != other.mNegated)
			return false;
		
		//TODO: something efficient
		for (int i = 0; i < mRepetitionSignature.size(); i++) {
			if (!mRepetitionSignature.get(i).containsAll(other.mRepetitionSignature.get(i)))
					return false;
			if (!other.mRepetitionSignature.get(i).containsAll(mRepetitionSignature.get(i)))
					return false;
		}
		for (int i = 0; i < mExceptReflSignature.size(); i++) {
			if (!mExceptReflSignature.get(i).containsAll(other.mExceptReflSignature.get(i)))
					return false;
			if (!other.mExceptReflSignature.get(i).containsAll(mExceptReflSignature.get(i)))
					return false;
		}
		
		return true;
	}

	@Override
	public int hashCode() {
		// TODO do something smarter
		return 0;
	}

	@Override
	public String toString() {
		return " -<" + mRepetitionSignature.toString() + ", " + mExceptReflSignature.toString() + ", " + mNegated + ">";
	}

	/**
	 * Checks if "this" and "other" are complements in the sense that, say, "this"
	 * talks about only reflexive points and "other" only talks about non-reflexive 
	 * points.
	 * Returns the joined signature (i.e. the one covering both reflexive and non-
	 *  reflexive points), null if the two aren't complements
	 */
	public AAAtomSignature joinComplementary(AAAtomSignature other) {
		assert this.mRepetitionSignature.size() == other.mRepetitionSignature.size();
		
		if (this.mNegated != other.mNegated)
			return null;
		
		assert this.mRepetitionSignature.size() == 2;
		//TODO: support ternary and more
		
		//repetition signature has to be the same
		for (int i = 0; i < this.mRepetitionSignature.size(); i++) {
			if (!this.mRepetitionSignature.get(i).containsAll(other.mRepetitionSignature.get(i)))
				return null;
			if (!other.mRepetitionSignature.get(i).containsAll(this.mRepetitionSignature.get(i)))
				return null;
		}
		// exceptrefl signature has to complement (trivial for size 2)
		if (this.mExceptReflSignature.size() + other.mExceptReflSignature.size() != 1)
			return null;
		
		//complement case --> return the joined signature
		HashSet<Integer> hs1 = new HashSet<Integer>();
		hs1.add(1);
		HashSet<Integer> hs2 = new HashSet<Integer>();
		hs2.add(2);
		ArrayList<HashSet<Integer>> al = new ArrayList<HashSet<Integer>>();
		al.add(hs1);
		al.add(hs2);
		return new AAAtomSignature(al, new ArrayList<>(0), this.mNegated);
	}
}
