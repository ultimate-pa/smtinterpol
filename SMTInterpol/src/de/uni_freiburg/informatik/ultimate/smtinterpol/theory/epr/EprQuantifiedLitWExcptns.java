package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

public class EprQuantifiedLitWExcptns {
	
	// Literals polarity
	boolean mIsPositive;

	// quantified atom
	EprQuantifiedPredicateAtom mAtom;

	// excepted points
	HashMap<TermVariable, HashSet<ApplicationTerm>> mExceptedPoints;

	// explanation
	EprClause mExplanation;
//	Clause mExplanation;

	public EprQuantifiedLitWExcptns(boolean isPositive, EprQuantifiedPredicateAtom atom, 
			HashMap<TermVariable, HashSet<ApplicationTerm>> ePoints,
			EprClause explanation) {
		mIsPositive = isPositive;
		mAtom = atom;
		mExceptedPoints = ePoints;
		mExplanation = explanation;
	}

	public String toString() {
		String not = mIsPositive ? "" : "! ";
		return  not + mAtom.toString() + "\\" + mExceptedPoints.toString();
	}

	public Literal getLiteral() {
		return mIsPositive ? mAtom : mAtom.negate();
	}
}
