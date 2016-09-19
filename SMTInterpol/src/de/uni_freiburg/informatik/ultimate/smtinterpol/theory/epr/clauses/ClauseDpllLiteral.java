package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.Set;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;

public class ClauseDpllLiteral extends ClauseLiteral {

	public ClauseDpllLiteral(boolean polarity, DPLLAtom atom, EprClause clause, EprTheory eprTheory) {
		super(polarity, atom, clause, eprTheory);
		assert !(atom instanceof EprPredicateAtom) : "use different ClauseLiteral";
		assert !(atom instanceof EprQuantifiedEqualityAtom) : "use different ClauseLiteral";
	}

	/**
	 * 
	 * @param decideStackBorder this parameter is irrelevant for dpll literals because they lie
	 *   "below" the epr decide stack anyway.
	 */
	@Override
	protected ClauseLiteralState determineState(DecideStackLiteral decideStackBorder) {
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
	
	public Clause getUnitGrounding(Literal literal) {
		IDawg<ApplicationTerm, TermVariable> groundingDawg = getClause().getClauseLitToUnitPoints().get(this);

		assert this.getLiteral() == literal;
		assert literal.getAtom().getSMTFormula(mEprTheory.getTheory()).getFreeVars().length == 0;
		assert groundingDawg != null && ! groundingDawg.isEmpty();

		//TODO: sample one point from the dawg, so we give a one-point dawg to getGroundings() ?..
		Set<Clause> groundings = getClause().getGroundings(groundingDawg);
		
		return groundings.iterator().next();
	}
}
