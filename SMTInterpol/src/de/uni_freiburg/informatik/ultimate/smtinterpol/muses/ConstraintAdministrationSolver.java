package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;

import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A class that wraps a script and provides additional functionality for the MUS enumeration. Basically, it is used for
 * administration of the constraints and communication with the solver. It provides recursion levels that
 * enhance the reusability of the solver in ReMUS. The earlier recursion levels only contain critical constraints. The
 * latest recursion level is divided in two "usual" push/pop levels: The lower level again contains critical
 * constraints. The upper level contains all constraints which status is currently unknown. Also this class translates
 * between the bitset representation and the term representation of constraints for the solver.
 *
 * @author LeonardFichtner
 *
 */
public class ConstraintAdministrationSolver {

	final Script mScript;
	boolean mUnknownConstraintsAreSet;
	int mLevels;
	Translator mTranslator;

	/**
	 * Note: This constructor does not reset the given script.
	 */
	public ConstraintAdministrationSolver(final Script script, final Translator translator) {
		mScript = script;
		mUnknownConstraintsAreSet = false;
		mLevels = 0;
		mTranslator = translator;
	}

	/**
	 * This pushes a new recursion level. That means, one can not modify any previously asserted terms, until
	 * popRecLevel is called. No unknown constraints are allowed to be asserted when pushing a new recursion level.
	 */
	public void pushRecLevel() {
		if (mUnknownConstraintsAreSet) {
			throw new SMTLIBException("You may not push a new recursion level, when unknown constraints are set.");
		}
		push(1);
	}

	/**
	 * This pops the current recursion level and thereby the assertions from the previous recursion level are modifiable
	 * again.
	 */
	public void popRecLevel() {
		clearUnknownConstraints();
		pop(1);
	}

	/**
	 * Clear all Unknown constraints.
	 */
	public void clearUnknownConstraints() {
		if (mUnknownConstraintsAreSet) {
			pop(1);
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
		mScript.assertTerm(mTranslator.translate2Constraint(constraintNumber));
	}

	/**
	 * Assert critical constraints. This can only be done, when no unknown constraints are asserted.
	 */
	public void assertCriticalConstraints(final BitSet constraints) throws SMTLIBException {
		if (mUnknownConstraintsAreSet) {
			throw new SMTLIBException("Modifying crits without clearing unknowns is prohibited.");
		}
		for (int i = constraints.nextSetBit(0); i >= 0; i = constraints.nextSetBit(i + 1)) {
			mScript.assertTerm(mTranslator.translate2Constraint(i));
		}
	}

	/**
	 * Assert a constraint, for which it is not known whether it is critical or not.
	 */
	public void assertUnknownConstraint(final int constraintNumber) {
		if (!mUnknownConstraintsAreSet) {
			push(1);
			mUnknownConstraintsAreSet = true;
		}
		mScript.assertTerm(mTranslator.translate2Constraint(constraintNumber));
	}

	/**
	 * Assert constraints, for which it is not known whether they are critical or not.
	 */
	public void assertUnknownConstraints(final BitSet constraints) {
		if (!mUnknownConstraintsAreSet) {
			push(1);
			mUnknownConstraintsAreSet = true;
		}
		for (int i = constraints.nextSetBit(0); i >= 0; i = constraints.nextSetBit(i + 1)) {
			mScript.assertTerm(mTranslator.translate2Constraint(i));
		}
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
		return mTranslator.translateToBitSet(core);
	}

	/**
	 * Try to extend the currently asserted satisfiable set to a bigger satisfiable set without investing too much work
	 * in it.
	 */
	public BitSet getSatExtension() throws SMTLIBException, UnsupportedOperationException {
		if (!(LBool.SAT == mScript.checkSat())) {
			throw new SMTLIBException("The current assertions are not satisfiable.");
		}
		final Model model = mScript.getModel();
		final Term[] assertions = mScript.getAssertions();
		final BitSet assertedAsBits = mTranslator.translateToBitSet(assertions);
		final BitSet notAsserted = (BitSet) assertedAsBits.clone();
		notAsserted.flip(0, mTranslator.getNumberOfConstraints());

		for (int i = notAsserted.nextSetBit(0); i >= 0; i = notAsserted.nextSetBit(i + 1)) {
			final Term evaluatedTerm = model.evaluate(mTranslator.translate2Constraint(i));
			if (evaluatedTerm == evaluatedTerm.getTheory().mTrue) {
				assertedAsBits.set(i);
			} else if (evaluatedTerm == evaluatedTerm.getTheory().mFalse) {
				// do nothing
			} else {
				// If this happens, evaluate does not work as planned
				throw new SMTLIBException("Term evaluated by model is neither True nor False.");
			}
		}
		return assertedAsBits;
	}

	/**
	 * Try to extend the currently asserted satisfiable set to a bigger satisfiable set, but invest more work in it,
	 * than {@link #getSatExtension(BitSet)}.
	 */
	public BitSet getSatExtensionMoreDemanding() throws SMTLIBException {
		if (!(LBool.SAT == mScript.checkSat())) {
			throw new SMTLIBException("The current assertions are not satisfiable.");
		}
		push(1);
		final Term[] assertions = mScript.getAssertions();
		final BitSet assertedAsBits = mTranslator.translateToBitSet(assertions);
		final BitSet notAsserted = (BitSet) assertedAsBits.clone();
		notAsserted.flip(0, mTranslator.getNumberOfConstraints());

		for (int i = notAsserted.nextSetBit(0); i >= 0; i = notAsserted.nextSetBit(i + 1)) {
			mScript.assertTerm(mTranslator.translate2Constraint(i));
			assertedAsBits.set(i);
			switch (mScript.checkSat()) {
			case UNSAT:
				assertedAsBits.clear(i);
				pop(1);
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
		if (!(LBool.SAT == mScript.checkSat())) {
			throw new SMTLIBException("The current assertions are not satisfiable.");
		}
		push(1);
		int pushCounter = 1;
		final Term[] assertions = mScript.getAssertions();
		final BitSet assertedAsBits = mTranslator.translateToBitSet(assertions);
		final BitSet notAsserted = (BitSet) assertedAsBits.clone();
		notAsserted.flip(0, mTranslator.getNumberOfConstraints());

		for (int i = notAsserted.nextSetBit(0); i >= 0; i = notAsserted.nextSetBit(i + 1)) {
			push(1);
			mScript.assertTerm(mTranslator.translate2Constraint(i));
			pushCounter++;
			assertedAsBits.set(i);
			switch (mScript.checkSat()) {
			case UNSAT:
				assertedAsBits.clear(i);
				pop(1);
				pushCounter--;
				break;
			case SAT:
				break;
			case UNKNOWN:
				throw new SMTLIBException("Solver returns LBool.UNKNOWN in extension process.");
			default:
				throw new SMTLIBException("Unknown LBool value in extension process.");
			}
		}
		pop(pushCounter);
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
		return mTranslator.translateToBitSet(crits);
	}

	/**
	 * Return a proof of unsatisfiability according to {@link Script#getProof()}.
	 */
	public Term getProof() throws SMTLIBException, UnsupportedOperationException {
		return mScript.getProof();
	}

	/**
	 * Returns the number of declared constraints.
	 */
	public int getNumberOfConstraints() {
		return mTranslator.getNumberOfConstraints();
	}

	public ArrayList<Integer> randomPermutation(final BitSet toBePermutated) {
		final ArrayList<Integer> toBePermutatedList = new ArrayList<>();
		for (int i = toBePermutated.nextSetBit(0); i >= 0; i = toBePermutated.nextSetBit(i + 1)) {
			toBePermutatedList.add(i);
		}
		java.util.Collections.shuffle(toBePermutatedList);
		return toBePermutatedList;
	}

	private void push(final int levels) {
		mLevels++;
		mScript.push(levels);
	}

	private void pop(final int levels) {
		mLevels = mLevels - levels;
		assert mLevels >= 0 : "This class should not be able to modify lower levels of the script than the level "
				+ "at which it was created";
		mScript.pop(levels);
	}
}
