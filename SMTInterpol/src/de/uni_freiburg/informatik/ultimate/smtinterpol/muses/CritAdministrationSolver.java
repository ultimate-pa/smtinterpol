package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A class that wraps a script and provides additional functionality for the MUS enumeration. Basically, it is used for
 * administration of the critical constraints. It provides recursion levels that enhance the reusability of the solver
 * in ReMUS. The earlier recursion levels only contain critical constraints. The latest recursion level is divided in
 * two "usual" push/pop levels: The lower level again contains critical constraints. The upper level contains all
 * constraints which status is currently unknown. Also this class translates between the bitset representation and the
 * term representation of constraints for the solver.
 *
 * @author LeonardFichtner
 *
 */
public class CritAdministrationSolver {

	final Script mScript;
	boolean mUnknownConstraintsAreSet;
	HashMap<AnnotatedTerm, Integer> mConstraint2Index;
	ArrayList<AnnotatedTerm> mIndex2Constraint;

	/**
	 * Note: This constructor does reset the assertions of the given script.
	 */
	public CritAdministrationSolver(final Script script) {
		mScript = script;
		mScript.resetAssertions();
		mUnknownConstraintsAreSet = false;
		mConstraint2Index = new HashMap<>();
		mIndex2Constraint = new ArrayList<>();
	}

	/**
	 * This pushes a new recursion level. That means, one can not modify any previously asserted terms, until
	 * popRecLevel is called. No unknown constraints are allowed to be asserted when pushing a new recursion level.
	 */
	public void pushRecLevel() {
		if (mUnknownConstraintsAreSet) {
			throw new SMTLIBException("You may not push a new recursion level, when unknown constraints are set.");
		}
		mScript.push(1);
	}

	/**
	 * This pops the current recursion level and thereby the assertions from the previous recursion level are modifiable
	 * again.
	 */
	public void popRecLevel() {
		if (mUnknownConstraintsAreSet) {
			mScript.pop(1);
		}
		mScript.pop(1);
	}

	/**
	 * Clear all Unknown constraints.
	 */
	public void clearUnknownConstraints() {
		if (mUnknownConstraintsAreSet) {
			mScript.pop(1);
			mUnknownConstraintsAreSet = false;
		}
	}

	/**
	 * Assert a critical constraint. This can only be done, when no unknown constraints are asserted.
	 */
	public void assertCriticalConstraint(final int constraintNumber) {
		if (mUnknownConstraintsAreSet) {
			throw new SMTLIBException("Modifying crits without clearing unknowns is prohibited.");
		}
		mScript.assertTerm(mIndex2Constraint.get(constraintNumber));
	}

	/**
	 * Assert a constraint, for which it is not known whether it is critical or not.
	 */
	public void assertUnknownConstraint(final int constraintNumber) {
		if (!mUnknownConstraintsAreSet) {
			mScript.push(1);
		}
		mScript.assertTerm(mIndex2Constraint.get(constraintNumber));
	}

	/**
	 * Check for satisfiability according to {@link Script#checkSat()}
	 */
	public LBool checkSat() {
		return mScript.checkSat();
	}

	/**
	 * Return an unsatisfiable core according to {@link Script#getUnsatCore}. This unsatCore will be returned as an
	 * array of booleans.
	 */
	public BitSet getUnsatCore() {
		final Term[] core = mScript.getUnsatCore();
		final BitSet coreAsBits = new BitSet(mIndex2Constraint.size());
		for(int i = 0; i < core.length; i++) {
			coreAsBits.set(mConstraint2Index.get(core[i]));
		}
		return coreAsBits;
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

	/**
	 * Return ALL critical constraints (this means on all recursion levels) that are asserted right now.
	 */
	public BitSet getCrits() {
		if (mUnknownConstraintsAreSet) {
			throw new SMTLIBException("Reading crits without clearing unknowns is prohibited.");
		}
		final Term[] crits = mScript.getAssertions();
		final BitSet critsAsBits = new BitSet();
		for(int i = 0; i < crits.length; i++) {
			critsAsBits.set(mConstraint2Index.get(crits[i]));
		}
		return critsAsBits;
	}

	/**
	 * Return a proof of unsatisfiability according to {@link Script#getProof()}.
	 */
	public Term getProof() {
		return mScript.getProof();
	}
}
