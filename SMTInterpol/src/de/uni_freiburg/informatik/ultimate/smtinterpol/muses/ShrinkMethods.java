package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.BitSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A class that provides methods for single MUS extraction.
 *
 * @author LeonardFichtner (leonard.fichtner@web.de)
 *
 */
public class ShrinkMethods {

	/*
	 * Takes an boolean array representing an unsatisfiable set of constraints and a CritAdministrationSolver,
	 * containing all criticals found so far, to generate a minimal unsatisfiable subset. This MUS will be returned as a
	 * new BitSet.
	 */
	public static BitSet shrink(final CritAdministrationSolver solver, final BitSet workingConstraints) {
		solver.pushRecLevel();
		final BitSet unknown = (BitSet) workingConstraints.clone();
		unknown.andNot(solver.getCrits());

		for (final int i = unknown.nextSetBit(0); i >= 0; unknown.nextSetBit(i + 1)) {
			for (final int j = unknown.nextSetBit(i + 1); j >= 0; unknown.nextSetBit(j + 1)) {
				solver.assertUnknownConstraint(j);
			}
			switch (solver.checkSat()) {
			// TODO: Add Extensions and BlockUp, BlockDown
			case UNSAT:
				unknown.clear(i);
				final BitSet core = solver.getUnsatCore();
				unknown.and(core);
				solver.clearUnknownConstraints();
				break;
			case SAT:
				solver.clearUnknownConstraints();
				solver.assertCriticalConstraint(i);
				break;
			case UNKNOWN:
				throw new SMTLIBException("Solver returns UNKNOWN in Shrinking process.");
			default:
				throw new SMTLIBException("Unknown LBool value in Shrinking process.");
			}
		}
		solver.clearUnknownConstraints();
		final Term proofOfMus = solver.getProof();
		final BitSet mus = solver.getCrits();
		solver.popRecLevel();
		return mus;
	}
}
