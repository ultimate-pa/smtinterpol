package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.BitSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A container made to keep minimal unsatisfiable subsets and their corresponding proof of unsatisfiability. The MUS is
 * represented as a BitSet, where the Bit at index i signals whether constraint number i is contained in the MUS. To
 * translate it into the corresponding constraints, {@link CritAdministratorSolver} must be used.
 *
 * @author LeonardFichtner
 *
 */
public class MUSContainer {

	BitSet mMus;
	Term mProof;

	public MUSContainer(final BitSet mus, final Term proof) {
		mMus = mus;
		mProof = proof;
	}

	public BitSet getMus() {
		return mMus;
	}

	public Term getProof() {
		return mProof;
	}
}
