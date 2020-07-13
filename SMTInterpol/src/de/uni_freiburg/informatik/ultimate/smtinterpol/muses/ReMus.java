package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

/**
 * This is an implementation of the ReMUS algorithm (see Recursive Online Enumeration of all Minimal Unsatisfiable
 * Subsets, Bendik et al.).
 *
 * @author LeonardFichtner
 *
 */
public class ReMus {

	ConstraintAdministrationSolver mSolver;
	UnexploredMap mMap;

	ArrayList<MusContainer> mMuses;
	boolean mProvisionalSat;
	BitSet mMaxUnexplored;
	BitSet mMcs;
	BitSet mPreviousCrits;
	BitSet mNewImpliedCrits;
	BitSet mWorkingSet;

	/**
	 * The solver and the map MUST have the same Translator.
	 */
	public ReMus(final ConstraintAdministrationSolver solver, final UnexploredMap map, final BitSet workingSet) {
		mSolver = solver;
		mMap = map;
		mWorkingSet = workingSet;
	}

	/**
	 * Applies the ReMUS algorithm to a set of constraints given as BitSet.
	 */
	public ArrayList<MusContainer> enumerate() throws SMTLIBException {
		// TODO: Implement Timeout
		mSolver.pushRecLevel();
		initializeMembers();
		mSolver.assertCriticalConstraints(mNewImpliedCrits);

		while (!mMaxUnexplored.isEmpty()) {
			if (mProvisionalSat) {
				handleUnexploredIsSat();
			} else {
				final BitSet unknowns = (BitSet) mMaxUnexplored.clone();
				mSolver.assertUnknownConstraints(unknowns);
				final LBool sat = mSolver.checkSat();
				mSolver.clearUnknownConstraints();
				if (sat == LBool.SAT) {
					handleUnexploredIsSat();
				} else if (sat == LBool.UNSAT) {
					handleUnexploredIsUnsat();
				} else {
					throw new SMTLIBException("CheckSat returns UNKNOWN in Mus enumeration process.");
				}
			}
			updateMembers();
			mSolver.assertCriticalConstraints(mNewImpliedCrits);
		}
		mSolver.popRecLevel();
		return mMuses;
	}

	private void initializeMembers() {
		mMuses = new ArrayList<>();
		mSolver.clearUnknownConstraints();
		mPreviousCrits = mSolver.getCrits();
		mMaxUnexplored = mMap.findMaximalUnexploredSubsetOf(mWorkingSet);
		mNewImpliedCrits = mMap.findImpliedCritsOf(mWorkingSet);
		mNewImpliedCrits.andNot(mPreviousCrits);
		// If maxUnexplored does not contain some of the known crits, it must be satisfiable
		mProvisionalSat = !Shrinking.contains(mMaxUnexplored, mPreviousCrits);
	}

	private void updateMembers() {
		mNewImpliedCrits.or(mPreviousCrits);
		mPreviousCrits = mNewImpliedCrits;
		mMaxUnexplored = mMap.findMaximalUnexploredSubsetOf(mWorkingSet);
		mNewImpliedCrits = mMap.findImpliedCritsOf(mWorkingSet);
		mNewImpliedCrits.andNot(mPreviousCrits);
		// If maxUnexplored does not contain some of the known crits, it must be satisfiable
		mProvisionalSat = !Shrinking.contains(mMaxUnexplored, mPreviousCrits);
	}

	private void handleUnexploredIsSat() {
		// To get an extension here is useless, since maxUnexplored is a MSS already
		mMap.BlockDown(mMaxUnexplored);
		mMcs = (BitSet) mWorkingSet.clone();
		mMcs.andNot(mMaxUnexplored);
		if (mMcs.cardinality() == 1) {
			mSolver.assertCriticalConstraint(mMcs.nextSetBit(0));
		} else {
			//We don't need mMaxUnexplored anymore before the update, so we can modify it directly
			final BitSet nextWorkingSet = mMaxUnexplored;
			for (int i = mMcs.nextSetBit(0); i >= 0; i = mMcs.nextSetBit(i + 1)) {
				mSolver.pushRecLevel();
				mSolver.assertCriticalConstraint(i);
				nextWorkingSet.set(i);
				final ReMus remus = new ReMus(mSolver, mMap, nextWorkingSet);
				mMuses.addAll(remus.enumerate());
				mSolver.popRecLevel();
				nextWorkingSet.clear(i);
			}
		}
	}

	private void handleUnexploredIsUnsat() {
		mSolver.pushRecLevel();
		final MusContainer musContainer = Shrinking.shrink(mSolver, mMaxUnexplored, mMap);
		mSolver.popRecLevel();
		mMuses.add(musContainer);
		final BitSet nextWorkingSet = (BitSet) musContainer.getMus().clone();
		// The somewhat arbitrary number 0.9 is a heuristic from the original paper
		if (nextWorkingSet.cardinality() < 0.9 * mMaxUnexplored.cardinality()) {
			for (int i = mMaxUnexplored.nextSetBit(0); nextWorkingSet.cardinality() < 0.9
					* mMaxUnexplored.cardinality(); i = mMaxUnexplored.nextSetBit(i + 1)) {
				if (!nextWorkingSet.get(i)) {
					nextWorkingSet.set(i);
				}
			}
			final ReMus remus = new ReMus(mSolver, mMap, nextWorkingSet);
			mMuses.addAll(remus.enumerate());
		}
	}
}
