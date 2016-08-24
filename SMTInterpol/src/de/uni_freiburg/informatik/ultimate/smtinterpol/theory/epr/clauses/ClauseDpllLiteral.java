package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;

public class ClauseDpllLiteral extends ClauseLiteral {

	public ClauseDpllLiteral(boolean polarity, DPLLAtom atom, EprClause clause, EprTheory eprTheory) {
		super(polarity, atom, clause, eprTheory);
		assert !(atom instanceof EprPredicateAtom) : "use different ClauseLiteral";
		assert !(atom instanceof EprQuantifiedEqualityAtom) : "use different ClauseLiteral";
	}

	@Override
	protected ClauseLiteralState determineState() {
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
