package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;

public class ClauseEprGroundLiteral extends ClauseEprLiteral {
	

	public ClauseEprGroundLiteral(boolean polarity, EprGroundPredicateAtom atom, 
			EprClause clause, EprTheory eprTheory) {
		super(polarity, atom, clause, eprTheory);
	}

	@Override
	protected ClauseLiteralState determineState() {
		assert false : "TODO: what about the DecideStackLiterals that impact this literal? "
				+ "(fields ClauseEprLiteral.mPartially...)";
		if (mAtom.getDecideStatus() == null) {
			// undecided 
			return ClauseLiteralState.Fulfillable;
		} else if ((mAtom.getDecideStatus() == mAtom) == mPolarity){
			// decided with same polarity
			return ClauseLiteralState.Fulfilled;
		} else {
			// decided with different polarity
			return ClauseLiteralState.Refuted;
		}
	}
	
}
