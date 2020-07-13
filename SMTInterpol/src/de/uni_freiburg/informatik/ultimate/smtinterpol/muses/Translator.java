package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;

/**
 * This class is responsible for translating between bit set representation and term representation of constraints.
 *
 * @author LeonardFichtner
 *
 */
public class Translator {

	HashMap<String, Integer> mNameOfConstraint2Index;
	ArrayList<NamedAtom> mIndex2AtomOfConstraint;
	int mNumberOfConstraints;

	public Translator() {
		mNameOfConstraint2Index = new HashMap<>();
		mIndex2AtomOfConstraint = new ArrayList<>();
		mNumberOfConstraints = 0;
	}

	/**
	 * The NamedAtom must be named by the AnnotatedTerm representing the constraint.
	 * Also the Polarity (preffered Status) must be set to TRUE for the Unexplored Map to behave correctly.
	 */
	public void declareConstraint(final NamedAtom atom) {
		final String name = getName(atom);
		mNameOfConstraint2Index.put(name, mNumberOfConstraints);
		mIndex2AtomOfConstraint.add(atom);
		mNumberOfConstraints++;
	}

	public Term translate2Constraint(final int index) {
		return getTerm(mIndex2AtomOfConstraint.get(index));
	}

	public NamedAtom translate2Atom(final int index) {
		return mIndex2AtomOfConstraint.get(index);
	}
	public int translate2Index(final Term term) {
		return mNameOfConstraint2Index.get(getName(term));
	}

	public int translate2Index(final NamedAtom atom) {
		return mNameOfConstraint2Index.get(getName(atom));
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

	public int getNumberOfConstraints() {
		return mNumberOfConstraints;
	}

	public ArrayList<NamedAtom> getIndex2AtomOfConstraint(){
		return mIndex2AtomOfConstraint;
	}

	private Term getTerm(final NamedAtom atom) {
		return atom.getSMTFormula(null, false);
	}
	private String getName(final NamedAtom atom) {
		return getName(atom.getSMTFormula(null, false));
	}

	private String getName(final Term term) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getName();
		} else if (term instanceof AnnotatedTerm) {
			return getName(((AnnotatedTerm) term).getAnnotations());
		} else {
			throw new SMTLIBException("Unknown type of term.");
		}
	}

	private String getName(final Annotation... annotation) throws SMTLIBException {
		String name = null;
		for (int i = 0; i < annotation.length; i++) {
			if (annotation[i].getKey().equals(":named")) {
				name = (String) annotation[i].getValue();
			}
		}
		if (name == null) {
			throw new SMTLIBException("No name for the constraint has been found.");
		}
		return name;
	}
}
