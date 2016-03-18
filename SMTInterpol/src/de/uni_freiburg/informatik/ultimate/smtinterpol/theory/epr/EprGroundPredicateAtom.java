package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class EprGroundPredicateAtom extends EprPredicateAtom {

	public EprGroundPredicateAtom(ApplicationTerm term, int hash, int assertionstacklevel, EprPredicate pred) {
		super(term, hash, assertionstacklevel, pred);
		assert term.getFreeVars().length == 0 : "trying to create a ground atom from a non-ground term";
		pred.addPointAtom(this.getArgumentsAsTermTuple(), this);
	}

	@Override
	public Term getSMTFormula(Theory smtTheory, boolean quoted) {
		// TODO Auto-generated method stub
//		return null;
		return mTerm;
	}

}
