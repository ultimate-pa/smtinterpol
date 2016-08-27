package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

/**
 * Represents a literal on the decide stack that was set because of a decision of the epr
 * solver (rather than a propagation..).
 * 
 * @author nutz
 */
public class DecideStackDecisionLiteral extends DecideStackQuantifiedLiteral {

	public DecideStackDecisionLiteral(boolean polarity, EprPredicate eprPredicate, IDawg dawg) {
		super(polarity, eprPredicate, dawg);
	}

	public DecideStackDecisionLiteral(boolean polarity, EprQuantifiedPredicateAtom atom,
			IDawg<ApplicationTerm, TermVariable> dawg) {
		super(polarity, atom, dawg);
		// TODO Auto-generated constructor stub
	}

}
