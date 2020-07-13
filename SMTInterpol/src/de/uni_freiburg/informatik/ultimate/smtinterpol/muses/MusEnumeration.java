package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

/**
 * Provides Methods for MUS Enumeration.
 *
 * @author LeonardFichtner
 *
 */
public class MusEnumeration {

	/**
	 * Applies the ReMUS algorithm to a set of constraints given as BitSet (see Recursive Online Enumeration of all
	 * Minimal Unsatisfiable Subsets, Bendik et al.). The solver and the map MUST have the same Translator.
	 */
	public static ArrayList<MusContainer> reMus(final ConstraintAdministrationSolver solver, final UnexploredMap map,
			final BitSet workingSet) throws SMTLIBException {
		// TODO: Implement Timeout
		final ArrayList<MusContainer> muses = new ArrayList<>();
		BitSet mcs;
		BitSet maxUnexplored = map.findMaximalUnexploredSubsetOf(workingSet);
		BitSet newCrits = map.findImpliedCritsOf(workingSet);
		BitSet previousCrits = solver.getCrits();
		// If maxUnexplored does not contain some of the known crits, it must be satisfiable
		boolean tentativeSat = !Shrinking.contains(maxUnexplored, previousCrits);
		newCrits.andNot(previousCrits);
		solver.assertCriticalConstraints(newCrits);

		while (!maxUnexplored.isEmpty()) {
			if (tentativeSat) {
				// use extension here? I think it is not worth it.
				map.BlockDown(maxUnexplored);
				mcs = (BitSet) workingSet.clone();
				mcs.andNot(maxUnexplored);
				if (mcs.cardinality() == 1) {
					solver.clearUnknownConstraints();
					solver.assertCriticalConstraint(mcs.nextSetBit(0));
				} else {
					final BitSet nextWorkingSet = (BitSet) workingSet.clone();
					for (int i = mcs.nextSetBit(0); i >= 0; i = mcs.nextSetBit(i + 1)) {
						solver.clearUnknownConstraints();
						solver.pushRecLevel();
						solver.assertCriticalConstraint(i);
						nextWorkingSet.set(i);
						muses.addAll(reMus(solver, map, nextWorkingSet));
						solver.popRecLevel();
						nextWorkingSet.clear(i);
					}
				}
			} else {
				final BitSet unknowns = (BitSet) maxUnexplored.clone();
				solver.assertUnknownConstraints(unknowns);
				if (solver.checkSat() == LBool.SAT) {
					// use extension here? I think it is not worth it.
					map.BlockDown(maxUnexplored);
					mcs = (BitSet) workingSet.clone();
					mcs.andNot(maxUnexplored);
					if (mcs.cardinality() == 1) {
						solver.clearUnknownConstraints();
						solver.assertCriticalConstraint(mcs.nextSetBit(0));
					} else {
						final BitSet nextWorkingSet = (BitSet) workingSet.clone();
						for (int i = mcs.nextSetBit(0); i >= 0; i = mcs.nextSetBit(i + 1)) {
							solver.clearUnknownConstraints();
							solver.pushRecLevel();
							solver.assertCriticalConstraint(i);
							nextWorkingSet.set(i);
							muses.addAll(reMus(solver, map, nextWorkingSet));
							nextWorkingSet.clear(i);
							solver.popRecLevel();
						}
					}
				} else if (solver.checkSat() == LBool.UNSAT) {
					final MusContainer musContainer = Shrinking.shrink(solver, maxUnexplored, map);
					muses.add(musContainer);
					final BitSet nextWorkingSet = (BitSet) musContainer.getMus().clone();
					// The somewhat arbitrary number 0.9 is a heuristic from the original paper
					if (nextWorkingSet.cardinality() < 0.9 * maxUnexplored.cardinality()) {
						for (int i = maxUnexplored.nextSetBit(0); nextWorkingSet.cardinality() < 0.9
								* maxUnexplored.cardinality(); i = maxUnexplored.nextSetBit(i + 1)) {
							if (!nextWorkingSet.get(i)) {
								nextWorkingSet.set(i);
							}
						}
						muses.addAll(reMus(solver, map, nextWorkingSet));
					}
				} else {
					throw new SMTLIBException("CheckSat returns UNKNOWN in Mus enumeration process.");
				}
			}
			maxUnexplored = map.findMaximalUnexploredSubsetOf(workingSet);
			newCrits = map.findImpliedCritsOf(workingSet);

			previousCrits = solver.getCrits();
			// If maxUnexplored does not contain some of the known crits, it must be satisfiable
			tentativeSat = !Shrinking.contains(maxUnexplored, previousCrits);
			newCrits.andNot(previousCrits);
			solver.assertCriticalConstraints(newCrits);
		}
		solver.popRecLevel();
		return muses;
	}
}
