package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

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
	public static boolean[] shrinkBase(final MUSSolver solver, final boolean[] constraints, final boolean[] crits) {
		solver.pushRecLevel();
		final boolean[] workingCrits = crits.clone();
		final boolean[] unknown = new boolean[constraints.length];
		for (int i = 1; i < constraints.length; i++) {
			unknown[i] = constraints[i] && !workingCrits[i];
		}

		for (int i = 1; i < unknown.length; i++) {
			for (int j = i; j < unknown.length; j++) {
				if (unknown[i] && !workingCrits[i]) {
					solver.assertUnknownConstraint(i);
				}
			}
			switch (solver.checkSat()) {
			case UNSAT:
				unknown[i - 1] = false;
				final boolean[] core = solver.getUnsatCore();
				for(int k = 0; k < unknown.length; k++) {
					if (core[i]) {
						unknown[i] = false;
					}
				}
				break;
			case SAT:
				solver.assertCriticalConstraint(i - 1);
				workingCrits[i - 1] = true;
				break;
			case UNKNOWN:
				break;
			default:
				break;
			}
		}
		solver.popRecLevel();
		return workingCrits;
	}
}
