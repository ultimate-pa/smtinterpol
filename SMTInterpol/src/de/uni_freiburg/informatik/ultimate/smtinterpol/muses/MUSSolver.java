package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

/**
 * A class that wraps a script and provides additional functionality for the MUS enumeration. It provides recursion
 * levels that enhance the reusability of the solver in ReMUS. Every recursion level is divided in two "usual" push/pop
 * levels: The lower level contains all crits. The upper level contains all constraints which status is currently
 * unknown.
 *
 * @author LeonardFichtner
 *
 */
public class MUSSolver {

	final Script script;
	boolean hasPushedSinceLevelUp;

	/**
	 * Note: This constructor does not reset the given script.
	 */
	public MUSSolver(final Script script) {
		this.script = script;
		hasPushedSinceLevelUp = false;
	}

	/**
	 * This pushes a new recursion level. That means, one can not modify any previously asserted terms, until
	 * popRecLevel is called.
	 */
	public void pushRecLevel() {

	}

	/**
	 * This pops the current recursion level and thereby the assertions from the previous recursion level are modifiable
	 * again.
	 */
	public void popRecLevel() {

	}

	/**
	 * Assert a constraint that has is critical.
	 */
	public void assertCriticalConstraint(final int constraintNumber) {
		if (hasPushedSinceLevelUp) {
			script.pop(1);
		}

	}

	/**
	 * Assert a constraint, for which it is not known whether it is critical or not.
	 */
	public void assertUnknownConstraint(final int constraintNumber) {

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
	public boolean[] getUnsatCore() {
		// TODO: Implement this, after it is clear what representation for MUSes we use.
		return new boolean[0];
	}
}
