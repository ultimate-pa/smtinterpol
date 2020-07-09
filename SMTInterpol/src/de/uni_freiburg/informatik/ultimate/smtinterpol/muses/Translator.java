package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This class is responsible for translating between bit set representation and term representation of constraints.
 *
 * @author LeonardFichtner
 *
 */
public class Translator {

	HashMap<String, Integer> mNameOfConstraint2Index;
	ArrayList<AnnotatedTerm> mIndex2Constraint;
	int mNumberOfConstraints;

	public Translator() {
		mNameOfConstraint2Index = new HashMap<>();
		mIndex2Constraint = new ArrayList<>();
		mNumberOfConstraints = 0;
	}

	public void declareConstraint(final AnnotatedTerm term) {
		final String name = getName(term);
		mNameOfConstraint2Index.put(name, mNumberOfConstraints);
		mIndex2Constraint.add(term);
		mNumberOfConstraints++;
	}

	public Term translate2Constraint(final int index) {
		return mIndex2Constraint.get(index);
	}

	public int translate2Index(final Term term) {
		return mNameOfConstraint2Index.get(getName(term));
	}

	/**
	 * Translates the arrays of Terms that are returned by the script to the corresponding BitSet.
	 */
	public BitSet translateToBitSet(final Term[] constraints) {
		final BitSet constraintsAsBits = new BitSet(mNumberOfConstraints);
		for (int i = 0; i < constraints.length; i++) {
			constraintsAsBits.set(translate2Index(constraints[i]));
		}
		return constraintsAsBits;
	}

	public String getName(final Term term) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getName();
		} else if (term instanceof AnnotatedTerm) {
			return getName(((AnnotatedTerm) term).getAnnotations());
		} else {
			throw new SMTLIBException("Unknown type of term.");
		}
	}

	public int getNumberOfConstraints() {
		return mNumberOfConstraints;
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
}
