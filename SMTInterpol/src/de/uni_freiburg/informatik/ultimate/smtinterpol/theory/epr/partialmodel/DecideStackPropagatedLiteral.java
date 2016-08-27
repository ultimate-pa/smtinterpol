package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

/**
 * Represents a literal on the epr decide stack that was set because of a unit propagation.
 * 
 * @author nutz
 *
 */
public class DecideStackPropagatedLiteral extends DecideStackQuantifiedLiteral {
	
	/**
	 * the clause that, together with the prefix of the decide stack is responsible
	 * for the setting of this literal
	 */
	EprClause mUnitClause;

	public DecideStackPropagatedLiteral(boolean polarity, EprQuantifiedPredicateAtom atom,
			IDawg<ApplicationTerm, TermVariable> dawg, EprClause unitClause) {
		super(polarity, atom, dawg);
		mUnitClause = unitClause;
	}
}
