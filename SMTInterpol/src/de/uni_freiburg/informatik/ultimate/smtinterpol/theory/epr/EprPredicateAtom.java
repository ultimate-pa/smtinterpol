package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;

public class EprPredicateAtom extends EprAtom {

	private final FunctionSymbol mPredicate;

	public EprPredicateAtom(ApplicationTerm term, int hash, int assertionstacklevel, FunctionSymbol predicate) {
		super(term, hash, assertionstacklevel);
		mPredicate = predicate;
	}
	
	public FunctionSymbol getPredicate() {
		return mPredicate;
	}

}
