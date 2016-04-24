package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

/**
 * Stands for a clause of that contains one quantified literal built from an uninterpreted predicate,
 * and an arbitrary number of quantified equalities.
 * The predicate literal may be positive or negative, the equalities must be positive.
 *  example: (or (not (P x y z a)) (= x a) (= x b) (= y z) ...)
 *  
 * @author nutz
 */
public class EprQuantifiedLitWExcptns {
	
	// the Literal's polarity
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
