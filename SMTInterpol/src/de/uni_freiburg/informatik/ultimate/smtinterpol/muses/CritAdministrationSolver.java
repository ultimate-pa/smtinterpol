package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A class that wraps a script and provides additional functionality for the MUS enumeration. Basically, it is used for
 * administration of the critical constraints and communication with the solver. It provides recursion levels that
 * enhance the reusability of the solver in ReMUS. The earlier recursion levels only contain critical constraints. The
 * latest recursion level is divided in two "usual" push/pop levels: The lower level again contains critical
 * constraints. The upper level contains all constraints which status is currently unknown. Also this class translates
 * between the bitset representation and the term representation of constraints for the solver.
 *
 * @author LeonardFichtner
 *
 */
public class CritAdministrationSolver {

	final Script mScript;
	boolean mUnknownConstraintsAreSet;
	HashMap<String, Integer> mNameOfConstraint2Index;
	ArrayList<AnnotatedTerm> mIndex2Constraint;
	int mNumberOfConstraints;

	/**
	 * Note: This constructor does not reset the given script.
	 */
	public CritAdministrationSolver(final Script script) {
		mScript = script;
		mUnknownConstraintsAreSet = false;
		mNameOfConstraint2Index = new HashMap<>();
		mIndex2Constraint = new ArrayList<>();
		mNumberOfConstraints = 0;

		// This line is needed because of the convention that there is always a layer above the declared constraints.
		mScript.push(1);
	}

	/**
	 * Declare a constraint under a certain annotation. The annotation MUST include a name. The constraint can then be
	 * asserted by {@link #assertCriticalConstraint(int)} or {@link #assertUnknownConstraint(int)}. Note that this
	 * method can only be executed, when no constraints are asserted.
	 */
	public void declareConstraint(final Term constraint, final Annotation... annotation) throws SMTLIBException {
		if (!(mScript.getAssertions().length == 0)) {
			throw new SMTLIBException("Constraints must not be asserted, when a constraint is declared.");
		}
		mScript.pop(1);
		final String name = getName(annotation);

		mNameOfConstraint2Index.put(name, mNumberOfConstraints);
		mNumberOfConstraints++;

		final AnnotatedTerm annotatedConstraint = (AnnotatedTerm) mScript.annotate(constraint, annotation);
		mIndex2Constraint.add(annotatedConstraint);
		mScript.push(1);
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
			mUnknownConstraintsAreSet = true;
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
		return translateToBitSet(core);
	}

	/**
	 * Try to extend the currently asserted satisfiable set to a bigger satisfiable set without investing too much work
	 * in it.
	 */
	public BitSet getSatExtension() throws SMTLIBException, UnsupportedOperationException {
		final Model model = mScript.getModel();
		final Term[] assertions = mScript.getAssertions();
		final BitSet assertedAsBits = translateToBitSet(assertions);
		final BitSet notAsserted = (BitSet) assertedAsBits.clone();
		notAsserted.flip(0, mNumberOfConstraints);

		for (int i = notAsserted.nextSetBit(0); i >= 0; i = notAsserted.nextSetBit(i + 1)) {
			final Term evaluatedTerm = model.evaluate(mIndex2Constraint.get(i));
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
		mScript.push(1);
		final Term[] assertions = mScript.getAssertions();
		final BitSet assertedAsBits = translateToBitSet(assertions);
		final BitSet notAsserted = (BitSet) assertedAsBits.clone();
		notAsserted.flip(0, mNumberOfConstraints);

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
		final BitSet assertedAsBits = translateToBitSet(assertions);
		final BitSet notAsserted = (BitSet) assertedAsBits.clone();
		notAsserted.flip(0, mNumberOfConstraints);

		for (int i = notAsserted.nextSetBit(0); i >= 0; i = notAsserted.nextSetBit(i + 1)) {
			mScript.push(1);
			mScript.assertTerm(mIndex2Constraint.get(i));
			pushCounter++;
			assertedAsBits.set(i);
			switch (mScript.checkSat()) {
			case UNSAT:
				assertedAsBits.clear(i);
				mScript.pop(1);
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
		return translateToBitSet(crits);
	}

	/**
	 * Return a proof of unsatisfiability according to {@link Script#getProof()}.
	 */
	public Term getProof() throws SMTLIBException, UnsupportedOperationException {
		return mScript.getProof();
	}

	public int getNumberOfConstraints() {
		return mNumberOfConstraints;
	}

	public ArrayList<Integer> randomPermutation(final BitSet toBePermutated) {
		final ArrayList<Integer> toBePermutatedList = new ArrayList<>();
		for (int i = toBePermutated.nextSetBit(0); i >= 0; i = toBePermutated.nextSetBit(i + 1)) {
			toBePermutatedList.add(i);
		}
		java.util.Collections.shuffle(toBePermutatedList);
		return toBePermutatedList;
	}

	/**
	 * Translates the arrays of Terms that are returned by the script to the corresponding BitSet.
	 */
	private BitSet translateToBitSet(final Term[] constraints) {
		final BitSet constraintsAsBits = new BitSet(mNumberOfConstraints);
		for (int i = 0; i < constraints.length; i++) {
			final String name = getName(constraints[i]);
			constraintsAsBits.set(mNameOfConstraint2Index.get(name));
		}
		return constraintsAsBits;
	}

	private String getName(final Annotation... annotation) throws SMTLIBException {
		String name = null;
		for (int i = 0; i < annotation.length; i++) {
			if (annotation[i].getKey() == ":named") {
				name = (String) annotation[i].getValue();
			}
		}
		if (name == null) {
			throw new SMTLIBException("No name for the constraint has been found.");
		}
		return name;
	}

	private String getName(final Term term) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getName();
		}else if (term instanceof AnnotatedTerm) {
			return getName(((AnnotatedTerm) term).getAnnotations());
		}else {
			throw new SMTLIBException("Unknown type of term.");
		}
	}
}
