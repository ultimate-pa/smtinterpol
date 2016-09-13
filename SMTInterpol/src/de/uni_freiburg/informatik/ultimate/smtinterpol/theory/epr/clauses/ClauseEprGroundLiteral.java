package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

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

	@Override
	public boolean isDisjointFrom(IDawg<ApplicationTerm, TermVariable> dawg) {
		return ! dawg.accepts(EprHelpers.convertTermListToConstantList(mArgumentTerms));
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
