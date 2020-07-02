package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Model;
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
	public void assertCriticalConstraint(final int constraintNumber) throws SMTLIBException {
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
	public LBool checkSat() throws SMTLIBException {
		return mScript.checkSat();
	}

	/**
	 * Return an unsatisfiable core according to {@link Script#getUnsatCore}. This unsatCore will be returned as an
	 * array of booleans.
	 */
	public BitSet getUnsatCore() throws SMTLIBException, UnsupportedOperationException {
		final Term[] core = mScript.getUnsatCore();
		return arrayOfConstraintsToBitSet(core);
	}

	/**
	 * Try to extend the currently asserted satisfiable set to a bigger satisfiable set without investing too much work
	 * in it.
	 */
	public BitSet getSatExtension() throws SMTLIBException, UnsupportedOperationException {
		final Model model = mScript.getModel();
		final Term[] assertions = mScript.getAssertions();
		final BitSet assertedAsBits = arrayOfConstraintsToBitSet(assertions);
		final BitSet notAsserted = (BitSet) assertedAsBits.clone();
		notAsserted.flip(0, notAsserted.size());

		for (int i = notAsserted.nextSetBit(0); i >= 0; i = notAsserted.nextSetBit(i + 1)) {
			final Term evaluatedTerm = model.evaluate(mIndex2Constraint.get(i));
			//TODO: Implement when it is clear how to check whether a constraint is satisfied by a model
		}
		return new BitSet();
	}

	/**
	 * Try to extend the currently asserted satisfiable set to a bigger satisfiable set, but invest more work in it,
	 * than {@link #getSatExtension(BitSet)}.
	 */
	public BitSet getSatExtensionMoreDemanding() throws SMTLIBException {
		mScript.push(1);
		final Term[] assertions = mScript.getAssertions();
		final BitSet assertedAsBits = arrayOfConstraintsToBitSet(assertions);
		final BitSet notAsserted = (BitSet) assertedAsBits.clone();
		notAsserted.flip(0, notAsserted.size());

		for (int i = notAsserted.nextSetBit(0); i >= 0; i = notAsserted.nextSetBit(i + 1)) {
			mScript.assertTerm(mIndex2Constraint.get(i));
			assertedAsBits.set(i);
			switch (mScript.checkSat()) {
			case UNSAT:
				assertedAsBits.clear(i);
				mScript.pop(1);
				return assertedAsBits;
			case SAT:
				break;
			case UNKNOWN:
				throw new SMTLIBException("Solver returns UNKNOWN in Extension process.");
			default:
				throw new SMTLIBException("Unknown LBool value in Extension process.");
			}
		}
		throw new SMTLIBException(
				"This means, that the set of all constraints is satisfiable. Something is not right!");
	}

	/**
	 * Try to extend the currently asserted satisfiable set to a maximal satisfiable subset.
	 */
	public BitSet getSatExtensionMaximalDemanding() {
		mScript.push(1);
		int pushCounter = 1;
		final Term[] assertions = mScript.getAssertions();
		final BitSet assertedAsBits = arrayOfConstraintsToBitSet(assertions);
		final BitSet notAsserted = (BitSet) assertedAsBits.clone();
		notAsserted.flip(0, notAsserted.size());

		for (int i = notAsserted.nextSetBit(0); i >= 0; i = notAsserted.nextSetBit(i + 1)) {
			mScript.assertTerm(mIndex2Constraint.get(i));
			mScript.push(1);
			pushCounter++;
			assertedAsBits.set(i);
			switch (mScript.checkSat()) {
			case UNSAT:
				assertedAsBits.clear(i);
				mScript.pop(1);
				pushCounter--;
			case SAT:
				break;
			case UNKNOWN:
				throw new SMTLIBException("Solver returns UNKNOWN in Extension process.");
			default:
				throw new SMTLIBException("Unknown LBool value in Extension process.");
			}
		}
		mScript.pop(pushCounter);
		return assertedAsBits;
	}

	/**
	 * Return ALL critical constraints (this means on all recursion levels) that are asserted right now.
	 */
	public BitSet getCrits() throws SMTLIBException {
		if (mUnknownConstraintsAreSet) {
			throw new SMTLIBException("Reading crits without clearing unknowns is prohibited.");
		}
		final Term[] crits = mScript.getAssertions();
		return arrayOfConstraintsToBitSet(crits);
	}

	/**
	 * Return a proof of unsatisfiability according to {@link Script#getProof()}.
	 */
	public Term getProof() throws SMTLIBException, UnsupportedOperationException {
		return mScript.getProof();
	}

	public ArrayList<Integer> randomPermutation(final BitSet toBePermutated) {
		final ArrayList<Integer> toBePermutatedList = new ArrayList<>();
		for (int i = toBePermutated.nextSetBit(0); i >= 0; i = toBePermutated.nextSetBit(i + 1)) {
			toBePermutatedList.add(i);
		}
		java.util.Collections.shuffle(toBePermutatedList);
		return toBePermutatedList;
	}

	private BitSet arrayOfConstraintsToBitSet(final Term[] constraints) {
		final BitSet constraintsAsBits = new BitSet();
		for (int i = 0; i < constraints.length; i++) {
			constraintsAsBits.set(mConstraint2Index.get(constraints[i]));
		}
		return constraintsAsBits;
	}
}
