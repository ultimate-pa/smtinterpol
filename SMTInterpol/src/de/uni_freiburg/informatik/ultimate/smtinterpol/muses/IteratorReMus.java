package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Iterator;
import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

/**
 * This is an implementation of the ReMUS algorithm (see Recursive Online Enumeration of all Minimal Unsatisfiable
 * Subsets, Bendik et al.).
 *
 * @author LeonardFichtner
 *
 */
public class IteratorReMus implements Iterator<MusContainer> {

	ConstraintAdministrationSolver mSolver;
	UnexploredMap mMap;

	ArrayList<MusContainer> mMuses;
	boolean mProvisionalSat;
	BitSet mMaxUnexplored;
	BitSet mMcs;
	BitSet mPreviousCrits;
	BitSet mNewImpliedCrits;
	BitSet mWorkingSet;

	/*
	 * ============================================================================
	 * =========================================================================== NEW STUFF
	 */

	IteratorReMus mSubordinateRemus;
	boolean mMembersUpToDate;
	boolean mSatisfiableCaseLoopIsRunning;
	MusContainer mNextMus;
	int mLastSatisfiableCaseLoopRunningIndex;
	BitSet mSatisfiableCaseLoopNextWorkingSet;

	/**
	 * The solver and the map MUST have the same Translator. ReMUS assumes ownership over the solver and the map.
	 */
	public IteratorReMus(final ConstraintAdministrationSolver solver, final UnexploredMap map,
			final BitSet workingSet) {
		mSolver = solver;
		mMap = map;
		if (workingSet.length() > mSolver.getNumberOfConstraints()) {
			throw new SMTLIBException(
					"There are constraints set in the workingSet that are not registered in the translator of the "
							+ "solver and the map");
		}
		mWorkingSet = workingSet;
		initializeMembers();
	}

	@Override
	public boolean hasNext() throws SMTLIBException {
		if (mNextMus != null) {
			return true;
		}

		if (mSubordinateRemus != null && mSubordinateRemus.hasNext()) {
			mNextMus = mSubordinateRemus.next();
			return true;
		} else {
			removeSubordinateRemus();
		}

		if (mSatisfiableCaseLoopIsRunning) {
			resumeSatisfiableCaseLoopUntilNextMus();
		}
		if (mNextMus != null) {
			return true;
		}

		searchForNextMusInThisRecursionLevel();
		if (mNextMus != null) {
			return true;
		}

		return false;
	}

	@Override
	public MusContainer next() throws SMTLIBException {
		if (hasNext()) {
			final MusContainer nextMus = mNextMus;
			mNextMus = null;
			return nextMus;
		}else {
			throw new NoSuchElementException();
		}
	}

	/**
	 * Finds and returns the rest of the muses.
	 */
	public ArrayList<MusContainer> enumerate() throws SMTLIBException {
		final ArrayList<MusContainer> restOfMuses = new ArrayList<>();
		while(hasNext()) {
			restOfMuses.add(next());
		}
		return restOfMuses;
	}

	private void createNewSubordinateRemus(final BitSet nextWorkingSet) {
		mSolver.pushRecLevel();
		mSubordinateRemus = new IteratorReMus(mSolver, mMap, nextWorkingSet);
	}

	private void createNewSubordinateRemusWithExtraCrit(final BitSet nextWorkingSet, final int crit) {
		mSolver.pushRecLevel();
		mSolver.assertCriticalConstraint(crit);
		mSubordinateRemus = new IteratorReMus(mSolver, mMap, nextWorkingSet);
	}

	private void removeSubordinateRemus() {
		if (mSubordinateRemus != null) {
			mSubordinateRemus = null;
			mSolver.popRecLevel();
		}
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
		mMembersUpToDate = true;
	}

	/**
	 * Updates Members and also asserts the newly found criticals right away.
	 */
	private void updateMembersAndAssertImpliedCrits() {
		mNewImpliedCrits.or(mPreviousCrits);
		mPreviousCrits = mNewImpliedCrits;
		mMaxUnexplored = mMap.findMaximalUnexploredSubsetOf(mWorkingSet);
		mNewImpliedCrits = mMap.findImpliedCritsOf(mWorkingSet);
		mNewImpliedCrits.andNot(mPreviousCrits);
		mSolver.assertCriticalConstraints(mNewImpliedCrits);
		// If maxUnexplored does not contain some of the known crits, it must be satisfiable
		mProvisionalSat = !Shrinking.contains(mMaxUnexplored, mPreviousCrits);
		mMembersUpToDate = true;
	}

	private void searchForNextMusInThisRecursionLevel() {
		if (mSubordinateRemus != null) {
			throw new SMTLIBException("Let the subordinate find it's muses first.");
		}

		if (!mMembersUpToDate) {
			updateMembersAndAssertImpliedCrits();
		}
		while (!mMaxUnexplored.isEmpty() && mNextMus == null) {
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
			//Don't updateMembers while another ReMus is in work, since in the update also crits are asserted
			//which will be removed (cause of popRecLevel) after the other Remus is finished.
			if (mSubordinateRemus == null) {
				updateMembersAndAssertImpliedCrits();
			}else {
				mMembersUpToDate = false;
			}
		}
	}

	private void handleUnexploredIsSat() {
		// To get an extension here is useless, since maxUnexplored is a MSS already. Also BlockUp is useless, since we
		// will block those sets anyways in the following recursion or have already blocked those sets
		mMap.BlockDown(mMaxUnexplored);
		mMcs = (BitSet) mWorkingSet.clone();
		mMcs.andNot(mMaxUnexplored);
		if (mMcs.cardinality() == 1) {
			mSolver.assertCriticalConstraint(mMcs.nextSetBit(0));
		} else {
			final BitSet nextWorkingSet = (BitSet) mMaxUnexplored.clone();
			int i = mMcs.nextSetBit(0);

			while (i >= 0 && mNextMus == null) {
				i = mMcs.nextSetBit(i + 1);
				mSolver.pushRecLevel();
				mSolver.assertCriticalConstraint(i);
				nextWorkingSet.set(i);
				createNewSubordinateRemus(nextWorkingSet);
				if (mSubordinateRemus.hasNext()) {
					mNextMus = mSubordinateRemus.next();
				} else {
					removeSubordinateRemus();
				}
				nextWorkingSet.clear(i);
				mLastSatisfiableCaseLoopRunningIndex = i;
				mSatisfiableCaseLoopNextWorkingSet = nextWorkingSet;
			}
			mSatisfiableCaseLoopIsRunning = i >= 0 ? true : false;
		}
	}

	private void resumeSatisfiableCaseLoopUntilNextMus() {
		int i = mMcs.nextSetBit(mLastSatisfiableCaseLoopRunningIndex + 1);
		while (i >= 0 && mNextMus == null) {
			mSatisfiableCaseLoopNextWorkingSet.set(i);
			createNewSubordinateRemusWithExtraCrit(mSatisfiableCaseLoopNextWorkingSet, i);
			if (mSubordinateRemus.hasNext()) {
				mNextMus = mSubordinateRemus.next();
			} else {
				removeSubordinateRemus();
			}
			mSatisfiableCaseLoopNextWorkingSet.clear(i);
			mLastSatisfiableCaseLoopRunningIndex = i;
			i = mMcs.nextSetBit(i + 1);
		}
		if (i < 0) {
			mSatisfiableCaseLoopIsRunning = false;
			return;
		}
	}

	private void handleUnexploredIsUnsat() {
		mSolver.pushRecLevel();
		mNextMus = Shrinking.shrink(mSolver, mMaxUnexplored, mMap);
		mSolver.popRecLevel();
		final BitSet nextWorkingSet = (BitSet) mNextMus.getMus().clone();
		// The somewhat arbitrary number 0.9 is a heuristic from the original paper
		if (nextWorkingSet.cardinality() < 0.9 * mMaxUnexplored.cardinality()) {
			for (int i = mMaxUnexplored.nextSetBit(0); nextWorkingSet.cardinality() < 0.9
					* mMaxUnexplored.cardinality(); i = mMaxUnexplored.nextSetBit(i + 1)) {
				if (!nextWorkingSet.get(i)) {
					nextWorkingSet.set(i);
				}
			}
			createNewSubordinateRemus(nextWorkingSet);
		}
	}
}
