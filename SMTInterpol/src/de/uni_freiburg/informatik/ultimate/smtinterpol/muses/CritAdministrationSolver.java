package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.BitSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

/**
 * A class that wraps a script and provides additional functionality for the MUS enumeration. Basically, it is used for
 * administration of the critical constraints. It provides recursion levels that enhance the reusability of the solver
 * in ReMUS. The earlier recursion levels only contain critical constraints. The latest recursion level is divided in
 * two "usual" push/pop levels: The lower level again contains critical constraints. The upper level contains all
 * constraints which status is currently unknown.
 *
 * @author LeonardFichtner
 *
 */
public class CritAdministrationSolver {

	final Script script;
	boolean unknownConstraintsAreSet;

	/**
	 * Note: This constructor does not reset the given script.
	 */
	public CritAdministrationSolver(final Script script) {
		this.script = script;
		unknownConstraintsAreSet = false;
	}

	/**
	 * This pushes a new recursion level. That means, one can not modify any previously asserted terms, until
	 * popRecLevel is called. No unknown constraints are allowed to be asserted when pushing a new recursion level.
	 */
	public void pushRecLevel() {
		if (unknownConstraintsAreSet) {
			throw new SMTLIBException("You may not push a new recursion level, when unknown constraints are set.");
		}
	}

	/**
	 * This pops the current recursion level and thereby the assertions from the previous recursion level are modifiable
	 * again.
	 */
	public void popRecLevel() {

	}

	/**
	 * Clear all Unknown constraints.
	 */
	public void clearUnknownConstraints() {
		if (unknownConstraintsAreSet) {
			script.pop(1);
			script.push(1);
		}
	}

	/**
	 * Assert a critical constraint. This can only be done, when no unknown constraints are asserted.
	 */
	public void assertCriticalConstraint(final int constraintNumber) {
		if (unknownConstraintsAreSet) {
			throw new SMTLIBException("Trying to modify crits without clearing unknowns.");
		}
		script.pop(1);

	}

	/**
	 * Assert a constraint, for which it is not known whether it is critical or not.
	 */
	public void assertUnknownConstraint(final int constraintNumber) {
		unknownConstraintsAreSet = true;
	}

	/**
	 * Check for satisfiability according to {@link Script#checkSat()}
	 */
	public LBool checkSat() {
		return script.checkSat();
	}

	/**
	 * Return an unsatisfiable core according to {@link Script#getUnsatCore}. This unsatCore will be returned as an
	 * array of booleans.
	 */
	public BitSet getUnsatCore() {
		// TODO: Implement this, after it is clear what representation for MUSes we use.
		return new boolean[0];
	}

	/**
	 * Try to extend the given satisfiable set to a bigger satisfiable set.
	 */
	public BitSet getSatExtension(final BitSet toBeExtended) {

	}

	/**
	 * Try to extend the given satisfiable set to a bigger satisfiable set, but invest more work in it, than
	 * {@link #getSatExtension(BitSet)}.
	 */
	public BitSet getSatExtensionDemanding(final BitSet toBeExtended) {

	}

	public BitSet getCrits() {

	}
}
