package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

public class EprQuantifiedPredicateAtom extends EprPredicateAtom {
	
	public EprQuantifiedPredicateAtom(ApplicationTerm term, int hash, int assertionstacklevel, EprPredicate pred) {
		super(term, hash, assertionstacklevel, pred);
		assert term.getFreeVars().length > 0 : "trying to create a quantified atom from a term that has free variables";
	}

	@Override
	public Term getSMTFormula(Theory smtTheory, boolean quoted) {
		return mTerm;
	}
}
