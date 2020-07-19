package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;

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
	long mDurationUntilTimeout;
	long mTimeout;
	TerminationRequest mTerminationRequest;

	ArrayList<MusContainer> mMuses;
	boolean mProvisionalSat;
	BitSet mMaxUnexplored;
	BitSet mMcs;
	BitSet mPreviousCrits;
	BitSet mNewImpliedCrits;
	BitSet mWorkingSet;

	/**
	 * The solver and the map MUST have the same Translator. ReMUS assumes ownership over the solver and the map.
	 * DurationUntilTimeout specifies how much time {@link #enumerate()} may run, until it should return the found
	 * muses. The durationUntilTimeout should be given in miliseconds. If the given durationUntilTimeout is negative,
	 * {@link #enumerate()} assumes to have infinite time.
	 */
	public ReMus(final ConstraintAdministrationSolver solver, final UnexploredMap map, final BitSet workingSet,
			final long durationUntilTimeout) {
		mSolver = solver;
		mMap = map;
		if (workingSet.length() > mSolver.getNumberOfConstraints()) {
			throw new SMTLIBException(
					"There are constraints set in the workingSet that are not registered in the translator of the "
							+ "solver and the map");
		}
		mWorkingSet = workingSet;
		mDurationUntilTimeout = durationUntilTimeout;
	}

	/**
	 * The solver and the map MUST have the same Translator. ReMUS assumes ownership over the solver and the map.
	 */
	public ReMus(final ConstraintAdministrationSolver solver, final UnexploredMap map, final BitSet workingSet) {
		this(solver, map, workingSet, -1);
	}

	/**
	 * Applies the ReMUS algorithm to a set of constraints given as BitSet.
	 */
	public ArrayList<MusContainer> enumerate() throws SMTLIBException {
		setTimeout();
		if (isTerminationRequested()) {
			return new ArrayList<>();
		}
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
			if (isTerminationRequested()) {
				mSolver.popRecLevel();
				return mMuses;
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
		//To get an extension here is useless, since maxUnexplored is a MSS already Also BlockUp is useless, since we
		//will block those sets anyways in the following recursion or have already blocked those sets
		mMap.BlockDown(mMaxUnexplored);
		mMcs = (BitSet) mWorkingSet.clone();
		mMcs.andNot(mMaxUnexplored);
		if (mMcs.cardinality() == 1) {
			mSolver.assertCriticalConstraint(mMcs.nextSetBit(0));
		} else {
			// We don't need mMaxUnexplored anymore before the update, so we can modify it directly
			final BitSet nextWorkingSet = mMaxUnexplored;
			for (int i = mMcs.nextSetBit(0); i >= 0; i = mMcs.nextSetBit(i + 1)) {
				mSolver.pushRecLevel();
				mSolver.assertCriticalConstraint(i);
				nextWorkingSet.set(i);
				final long timeLeft = mTimeout - System.currentTimeMillis();
				if (isTerminationRequested()) {
					mSolver.popRecLevel();
					return;
				}
				final ReMus remus = new ReMus(mSolver, mMap, nextWorkingSet, timeLeft);
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
			final long timeLeft = mTimeout - System.currentTimeMillis();
			if (isTerminationRequested()) {
				return;
			}
			final ReMus remus = new ReMus(mSolver, mMap, nextWorkingSet, timeLeft);
			mMuses.addAll(remus.enumerate());
		}
	}

	private void setTimeout() {
		if (mDurationUntilTimeout < 0) {
			mTimeout = Long.MAX_VALUE;
		} else {
			mTimeout = System.currentTimeMillis() + mDurationUntilTimeout;
		}
	}

	private boolean isTerminationRequested() {
		return System.currentTimeMillis() >= mTimeout;
	}
}
