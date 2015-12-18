package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.HashSet;

public class AAAtomSignature {

	/**
	 * Maps the nth argument to the indices of all arguments that have the same variable in the signature.
	 * (for example (P x y x) will yield the signature [{1,3}, {2}, {1,3}])
	 * TODO: find something more efficient
	 */
	private final ArrayList<HashSet<Integer>> signature;
	
	public AAAtomSignature(ArrayList<HashSet<Integer>> sig) {
		signature = sig;
	}
	
	/**
	 * 
	 * @param other
	 * @return true iff, by our assumed semantics, this implies other
	 */
	public boolean implies(AAAtomSignature other) {
		assert this.signature.size() == other.signature.size();

		//check:
		// at every point, the signatures partition must be subset of other's signature's partition..
		for (int i = 0; i < this.signature.size(); i++) 
			if (!other.signature.get(i).containsAll(this.signature.get(i)))
				return false;
		
		return true;
	}

	@Override
	public boolean equals(Object arg0) {
		if (!(arg0 instanceof AAAtomSignature)) return false;

		AAAtomSignature other = (AAAtomSignature) arg0;
		
		//TODO: something efficient
		for (int i = 0; i < signature.size(); i++) {
			if (!signature.get(i).containsAll(other.signature.get(i)))
					return false;
			if (!other.signature.get(i).containsAll(signature.get(i)))
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
		return signature.toString();
	}
}
