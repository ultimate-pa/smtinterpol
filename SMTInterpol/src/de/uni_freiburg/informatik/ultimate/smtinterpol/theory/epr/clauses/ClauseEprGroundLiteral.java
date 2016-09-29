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
		mIsStateDirty = false;
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

	@Override
	public Clause getGroundingForGroundLiteral(IDawg<ApplicationTerm, TermVariable> dawg, Literal groundLiteral) {
//		ApplicationTerm term = (ApplicationTerm) groundLiteral.getAtom().getSMTFormula(mEprTheory.getTheory());
//		List<ApplicationTerm> args = EprHelpers.convertTermArrayToConstantList(term.getParameters());
		// the groundings have nothing to do with the arguments of the ground literal in the sense that 
		//  there is no unification or so --> because we have a clause literal that is ground!
		// --> any grounding should work
		Set<Clause> groundings = getClause().getGroundings(dawg);
		assert !groundings.isEmpty();
		return groundings.iterator().next();
	}

}
