package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public abstract class EprPredicateAtom extends EprAtom {

	public final EprPredicate eprPredicate;
	TermTuple mArgsAsTermTuple = null;

	public EprPredicateAtom(ApplicationTerm term, int hash, int assertionstacklevel, EprPredicate pred) {
		super(term, hash, assertionstacklevel);
		assert term instanceof ApplicationTerm : "a predicate should always be an _Application_Term";
		eprPredicate = pred;
//		isQuantified = term.getFreeVars().length > 0;
	}
	
//	public EprPredicate getPredicate() {
//		return mPredicate;
//	}

	public Term[] getArguments() {
		return ((ApplicationTerm) mTerm).getParameters();
	}
	

	public TermTuple getArgumentsAsTermTuple() {
		if (mArgsAsTermTuple == null)
			mArgsAsTermTuple = new TermTuple(this.getArguments());
		return mArgsAsTermTuple;
	}

}
