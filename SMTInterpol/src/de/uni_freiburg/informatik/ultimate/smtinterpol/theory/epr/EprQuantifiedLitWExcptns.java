package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;

public class EprQuantifiedLitWExcptns {
	
	// Literals polarity
	boolean mIsPositive;

	// quantified atom
	EprQuantifiedPredicateAtom mAtom;

	// excepted points
	HashMap<TermVariable, ArrayList<ApplicationTerm>> mExceptedPoints;

	// explanation
	EprClause mExplanation;
//	Clause mExplanation;

	public EprQuantifiedLitWExcptns(boolean isPositive, EprQuantifiedPredicateAtom atom, 
			HashMap<TermVariable, ArrayList<ApplicationTerm>> ePoints,
			EprClause explanation) {
		mIsPositive = isPositive;
		mAtom = atom;
		mExceptedPoints = ePoints;
		mExplanation = explanation;
	}

	public String toString() {
		return mAtom.toString() + "\\" + mExceptedPoints.toString();
	}
}
