package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class EprQuantifiedAtomWithExceptions {

	// quantified atom
	EprQuantifiedPredicateAtom mAtom;

	// excepted points
	HashMap<TermVariable, ArrayList<ApplicationTerm>> mExceptedPoints;

	// explanation
	EprClause mExplanation;

	public EprQuantifiedAtomWithExceptions(EprQuantifiedPredicateAtom atom, 
			HashMap<TermVariable, ArrayList<ApplicationTerm>> ePoints,
			EprClause explanation) {
		mAtom = atom;
		mExceptedPoints = ePoints;
		mExplanation = explanation;
	}

}
