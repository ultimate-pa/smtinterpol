package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;

public class ClauseEprGroundLiteral extends ClauseLiteral {
	
	EprGroundPredicateAtom mAtom;

	public ClauseEprGroundLiteral(boolean polarity, EprGroundPredicateAtom atom, EprClause clause) {
		super(polarity, atom, clause);
		mAtom = atom;
	}
}
