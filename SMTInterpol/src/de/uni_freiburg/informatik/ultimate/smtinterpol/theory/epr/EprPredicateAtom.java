package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class EprPredicateAtom extends EprAtom {

	private final EprPredicate mPredicate;
	private final boolean mIsQuantified;

	public EprPredicateAtom(ApplicationTerm term, int hash, int assertionstacklevel, EprPredicate pred) {
		super(term, hash, assertionstacklevel);
		mPredicate = pred;
		mIsQuantified = term.getFreeVars().length > 0;
	}
	
	public EprPredicate getPredicate() {
		return mPredicate;
	}

	public Term[] getArguments() {
		return mTerm.getParameters();
	}

	public boolean isQuantified() {
		return mIsQuantified;
	}
}
