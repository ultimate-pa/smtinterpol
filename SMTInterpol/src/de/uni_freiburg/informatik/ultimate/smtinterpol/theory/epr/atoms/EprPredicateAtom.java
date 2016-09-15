package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;

public abstract class EprPredicateAtom extends EprAtom {

	public final EprPredicate mEprPredicate;

	public EprPredicateAtom(ApplicationTerm term, int hash, int assertionstacklevel, EprPredicate pred) {
		super(term, hash, assertionstacklevel);
		assert term instanceof ApplicationTerm : "a predicate should always be an _Application_Term";
		mEprPredicate = pred;
	}
	
	public EprPredicate getEprPredicate() {
		return mEprPredicate;
	}
}
