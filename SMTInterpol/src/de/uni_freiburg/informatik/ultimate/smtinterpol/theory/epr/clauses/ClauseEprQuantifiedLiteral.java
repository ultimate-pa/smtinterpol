package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;

public class ClauseEprQuantifiedLiteral extends ClauseLiteral {

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

	public ClauseEprQuantifiedLiteral(boolean polarity, EprQuantifiedPredicateAtom atom, EprClause clause) {
		super(polarity, atom, clause);
		mAtom = atom;
		
		for (int i = 0; i < atom.getArguments().length; i++) {
			if (! (atom.getArguments()[i] instanceof TermVariable))
				continue;
			TermVariable tv = (TermVariable) atom.getArguments()[i];
			clause.updateVariableToClauseLitToPosition(tv, this, i);
		}
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
}
