/*
 * Copyright (C) 2020 Leonard Fichtner
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * This class is responsible for translating between bit set representation and term representation of constraints.
 *
 * @author LeonardFichtner
 *
 */
public class Translator {

	ScopedHashMap<String, Integer> mNameOfConstraint2Index;
	ScopedArrayList<NamedAtom> mIndex2AtomOfConstraint;
	int mNumberOfConstraints;
	int mPushPopLevel;

	public Translator() {
		mNameOfConstraint2Index = new ScopedHashMap<>();
		mIndex2AtomOfConstraint = new ScopedArrayList<>();
		mNumberOfConstraints = 0;
		mPushPopLevel = 0;
	}

	/**
	 * The NamedAtom must be named by the AnnotatedTerm representing the constraint. Also the Polarity (preffered
	 * Status) must be set to TRUE for the Unexplored Map to behave correctly. If a term with the same name has already
	 * be declared, this method throws an SMTLIBException.
	 */
	public void declareConstraint(final NamedAtom atom) throws SMTLIBException {
		final String name = getName(atom);
		if (mNameOfConstraint2Index.containsKey(name)) {
			throw new SMTLIBException("This name does already exist.");
		}
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

	public ArrayList<NamedAtom> getIndex2AtomOfConstraint() {
		return mIndex2AtomOfConstraint;
	}

	/**
	 * Creates a new push/pop level for the declaration of Constraints.
	 */
	public void push() {
		mPushPopLevel++;
		mNameOfConstraint2Index.beginScope();
		mIndex2AtomOfConstraint.beginScope();
	}

	/**
	 * Makes the translator forget all declarations that have happened since the last push.
	 */
	public void pop() {
		if (mPushPopLevel == 0) {
			throw new SMTLIBException("You cannot pop levels when there aren't any levels.");
		}
		mNameOfConstraint2Index.endScope();
		mIndex2AtomOfConstraint.endScope();
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
