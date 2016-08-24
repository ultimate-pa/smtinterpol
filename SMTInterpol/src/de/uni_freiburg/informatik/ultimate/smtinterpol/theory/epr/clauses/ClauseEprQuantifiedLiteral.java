package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.IDawg;

public class ClauseEprQuantifiedLiteral extends ClauseEprLiteral {

	EprQuantifiedPredicateAtom mAtom;
	
	/**
	 * stores variable identities between different quantified literals in the same clause
	 * (for example would remember that in the clause {P(x, y), Q(y, z)} the second position of
	 *  the P-literal and the first position of the Q-literal have the same variable)
	 *  
	 *  Once we have filled this map, we can forget the concrete TermVariables.
	 */
	Map<Integer, Map<ClauseEprQuantifiedLiteral, Set<Integer>>> identicalVariablePositionsInOtherClauseLiterals = 
			new HashMap<Integer, Map<ClauseEprQuantifiedLiteral,Set<Integer>>>();
	
	/**
	 * Stores the points where this literal is currently fulfillable.
	 *  -- this is only updated on an isFulfillable query, so it should
	 *  only be non-null between a call to isFulfillable() and getFulfillablePoints()
	 */
	IDawg mFulfillablePoints;

	public ClauseEprQuantifiedLiteral(boolean polarity, EprQuantifiedPredicateAtom atom, 
			EprClause clause, EprTheory eprTheory) {
		super(polarity, atom, clause, eprTheory);
		mAtom = atom;
		

	}

	public void addExceptions(Set<EprQuantifiedEqualityAtom> quantifiedEqualities) {
		assert false : "TODO: implement";
	}

	/**
	 * Fill the map identicalVariablePositionsInOtherClauseLiterals
	 * (needs to be triggered after all literals have been added to the clause)
	 */
	public void updateIdenticalVariablePositions() {
		for (int i = 0; i < mAtom.getArguments().length; i++) {
			if (! (mAtom.getArguments()[i] instanceof TermVariable))
				continue;
			TermVariable tv = (TermVariable) mAtom.getArguments()[i];
			Map<ClauseEprQuantifiedLiteral, Set<Integer>> clToPos = mEprClause.getClauseLitToPositions(tv);

			for (Entry<ClauseEprQuantifiedLiteral, Set<Integer>> en : clToPos.entrySet()) {
				Map<ClauseEprQuantifiedLiteral, Set<Integer>> otherClToIdenticalPos = 
						identicalVariablePositionsInOtherClauseLiterals.get(i);
				
				if (otherClToIdenticalPos == null) {
					otherClToIdenticalPos = new HashMap<ClauseEprQuantifiedLiteral, Set<Integer>>();
					identicalVariablePositionsInOtherClauseLiterals.put(i, otherClToIdenticalPos);
				}
				otherClToIdenticalPos.put(en.getKey(), en.getValue());
			}
		}
	}

	/**
	 * Returns the points where this literal is fulfillable in the decide state that was current when
	 * isFulfillable was last called.
	 * To prevent some misusage, this nulls the field so it is not used twice.
	 *  --> however this will still be problematic if the state changes between the last call to isFulfillable
	 *  and this method.
	 * @return
	 */
	public IDawg getFulfillablePoints() {
		assert mFulfillablePoints != null;
		IDawg result = mFulfillablePoints;
		mFulfillablePoints = null;
		return result;
	}


	@Override
	protected ClauseLiteralState determineState() {
		IDawg union = mEprTheory.getDawgFactory().createEmptyDawg(null);//TODO
		for (DecideStackLiteral dsl : mPartiallyConflictingDecideStackLiterals) {
			union.addAll(dsl.getDawg());
		}
		mFulfillablePoints = union.complement();

		if (mFulfillablePoints.isEmpty()) {
			return ClauseLiteralState.Refuted;
		} else {
			return ClauseLiteralState.Fulfillable;
		}
	}
}
