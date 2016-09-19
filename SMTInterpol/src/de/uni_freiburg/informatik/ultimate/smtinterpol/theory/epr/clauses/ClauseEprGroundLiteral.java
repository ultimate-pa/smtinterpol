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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;

public class ClauseEprGroundLiteral extends ClauseEprLiteral {
	

	public ClauseEprGroundLiteral(boolean polarity, EprGroundPredicateAtom atom, 
			EprClause clause, EprTheory eprTheory) {
		super(polarity, atom, clause, eprTheory);
	}

	@Override

	/**
	 * 
	 * @param decideStackBorder (not sure if it is safe to ignore this parameter here.. TODO..)
	 */
	protected ClauseLiteralState determineState(DecideStackLiteral decideStackBorder) {
		if (mAtom.getDecideStatus() == null) {
			if (!mPartiallyConflictingDecideStackLiterals.isEmpty()) {
				assert mPartiallyConflictingDecideStackLiterals.size() == 1 : 
					"I thought we had the invariant that the epr decide stack literals are disjoint?..";
				return ClauseLiteralState.Refuted;
			}
			if (!mPartiallyFulfillingDecideStackLiterals.isEmpty()) {
				assert mPartiallyFulfillingDecideStackLiterals.size() == 1 : 
					"I thought we had the invariant that the epr decide stack literals are disjoint?..";
				return ClauseLiteralState.Fulfilled;
			}

			// decided neither by dpll engine nor by epr theory
			return ClauseLiteralState.Fulfillable;
		}
		

		if ((mAtom.getDecideStatus() == mAtom) == mPolarity){
			// decided with same polarity
			if (mPartiallyConflictingDecideStackLiterals != null
					&& !mPartiallyConflictingDecideStackLiterals.isEmpty()) {
				mEprTheory.getLogger().debug("EPRDEBUG: ClauseEprGroundLiteral.determineState(): " + this + 
						" already set as fulfilled by dpll engine, but has a refuting epr decide stack literal --> we must have a conflict");
			}

			return ClauseLiteralState.Fulfilled;
		} else {
			// decided with different polarity
			assert (mAtom.getDecideStatus() == mAtom) != mPolarity;
			if  (mPartiallyFulfillingDecideStackLiterals != null
					&& !mPartiallyFulfillingDecideStackLiterals.isEmpty()) {
				mEprTheory.getLogger().debug("EPRDEBUG: ClauseEprGroundLiteral.determineState(): " + this + 
						" already set as refuted by dpll engine, but has a fulfilling epr decide stack literal --> we must have a conflict");
			}
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
