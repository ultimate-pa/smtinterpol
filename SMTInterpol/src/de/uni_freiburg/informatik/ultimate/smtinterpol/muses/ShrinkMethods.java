package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.BitSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;

/**
 * A class that provides methods for single MUS extraction.
 *
 * @author LeonardFichtner (leonard.fichtner@web.de)
 *
 */
public class ShrinkMethods {

	/*
	 * Takes an boolean array representing an unsatisfiable set of constraints and known critical constraints of that
	 * set to generate a minimal unsatisfiable subset. This MUS will be returned as a new boolean array. It is assumed,
	 * that all known given crits are asserted before calling this method.
	 */
	public static BitSet shrinkBase(final MUSSolver solver, final BitSet constraints, final BitSet crits) {
		solver.pushRecLevel();
		final BitSet workingCrits = (BitSet) crits.clone();
		final BitSet unknown = (BitSet) constraints.clone();
		unknown.andNot(workingCrits);

		for (final int i = unknown.nextSetBit(0); i >= 0; unknown.nextSetBit(i+1)) {
			for (final int j = unknown.nextSetBit(i+1); j >= 0; unknown.nextSetBit(j + 1)) {
				solver.assertUnknownConstraint(j);
			}
			switch (solver.checkSat()) {
			case UNSAT:
				unknown.clear(i);
				final BitSet core = solver.getUnsatCore();
				unknown.and(core);
				solver.clearUnknownConstraints();
				break;
			case SAT:
				solver.clearUnknownConstraints();
				solver.assertCriticalConstraint(i);
				workingCrits.set(i);
				break;
			case UNKNOWN:
				throw new SMTLIBException("Solver returns UNKNOWN in Shrinking process.");
			default:
				throw new SMTLIBException("Unknown LBool value in Shrinking process.");
			}
		}
		solver.popRecLevel();
		return workingCrits;
	}
}
