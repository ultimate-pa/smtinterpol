package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.IEprLiteral;

public class EprGroundPredicateAtom extends EprPredicateAtom {

	public EprGroundPredicateAtom(ApplicationTerm term, int hash, int assertionstacklevel, EprPredicate pred) {
		super(term, hash, assertionstacklevel, pred);
		assert term.getFreeVars().length == 0 : "trying to create a ground atom from a non-ground term";
	}

	@Override
	public Term getSMTFormula(Theory smtTheory, boolean quoted) {
		return mTerm;
	}
}
