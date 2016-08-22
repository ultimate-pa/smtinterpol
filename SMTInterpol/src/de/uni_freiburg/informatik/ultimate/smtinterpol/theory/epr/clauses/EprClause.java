package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;

/**
 * Represents a clause that is only known to the EprTheory.
 * This means that the clause contains at least one free 
 * (implicitly quantified) variable.
 * 
 * @author nutz
 */
public class EprClause {

	final Set<Literal> mDpllLiterals;
	final EprTheory mEprTheory;

	final Set<ClauseLiteral> mLiterals;
	
	/**
	 * Stores for every variable that occurs in the clause for each literal in the
	 * clause at which position the variable occurs in the literal's atom (if at all).
	 */
	final Map<TermVariable, Map<ClauseEprQuantifiedLiteral, Set<Integer>>> mVariableToClauseLitToPositions;

	public EprClause(Set<Literal> lits, EprTheory eprTheory) {
		mDpllLiterals = lits;
		mEprTheory = eprTheory;
		mLiterals = createClauseLiterals(lits);
		mVariableToClauseLitToPositions = new HashMap<TermVariable, Map<ClauseEprQuantifiedLiteral, Set<Integer>>>();
	}

	private Set<ClauseLiteral> createClauseLiterals(Set<Literal> lits) {
		
		Set<ClauseLiteral> result = new HashSet<ClauseLiteral>();

		Set<EprQuantifiedEqualityAtom> quantifiedEqualities = new HashSet<EprQuantifiedEqualityAtom>();

		for (Literal l : lits) {
			boolean polarity = l.getSign() == 1;
			DPLLAtom atom = l.getAtom();
			
			if (atom instanceof EprQuantifiedPredicateAtom) {
				ClauseLiteral newL = new ClauseEprQuantifiedLiteral(
						polarity, (EprQuantifiedPredicateAtom) atom, this);
				result.add(newL);
				continue;
			} else if (atom instanceof EprGroundPredicateAtom) {
				ClauseLiteral newL = new ClauseEprGroundLiteral(
						polarity, (EprGroundPredicateAtom) atom, this);
				result.add(newL);
				continue;
			} else if (atom instanceof EprQuantifiedEqualityAtom) {
				// quantified equalities we don't add to the clause literals but 
				// just collect them for adding exceptions to the other quantified
				// clause literals later
				assert atom == l : "should have been eliminated by destructive equality reasoning";
				quantifiedEqualities.add((EprQuantifiedEqualityAtom) atom);
				continue;
			} else if (atom instanceof EprGroundEqualityAtom) {
				assert false : "do we really have this case?";
				continue;
//			} else if (atom instanceof CCEquality) {
//				(distinction form DPLLAtom does not seem necessary)
//				continue;
			} else {
				// atom is a "normal" Atom from the DPLLEngine
				result.add(new ClauseDpllLiteral(
						polarity, atom, this));
				continue;
			}
		}
		
		for (ClauseLiteral cl : result) {
			if (cl instanceof ClauseEprQuantifiedLiteral) {
				ClauseEprQuantifiedLiteral ceql = (ClauseEprQuantifiedLiteral) cl;
				// update all quantified predicate atoms according to the quantified equalities
				// by excluding the corresponding points in their dawgs
				ceql.addExceptions(quantifiedEqualities);

				// update the tracking of variable identities between quantified clause literals
				ceql.updateIdenticalVariablePositions();
			}
		}
		
		assert mLiterals.size() == mDpllLiterals.size() - quantifiedEqualities.size();
		return result;
	}


	/**
	 * This clause is informed that the DPLLEngine has set literal.
	 * The fulfillmentState of this clause may have to be updated because of this.
	 * 
	 * @param literal ground Epr Literal that has been set by DPLLEngine
	 */
	public void updateStateWrtDpllLiteral(Literal literal) {
		assert false : "TODO: implement";
	}

	public void backtrackStateWrtDpllLiteral(Literal literal) {
		assert false : "TODO: implement";
	}
	
	public Map<ClauseEprQuantifiedLiteral, Set<Integer>> getClauseLitToPositions(TermVariable tv) {
		return mVariableToClauseLitToPositions.get(tv);
	}
	
	public void updateVariableToClauseLitToPosition(TermVariable tv, ClauseEprQuantifiedLiteral ceql, Integer pos) {
		Map<ClauseEprQuantifiedLiteral, Set<Integer>> clToPos = mVariableToClauseLitToPositions.get(tv);
		Set<Integer> positions = null;

		if (clToPos == null) {
			clToPos = new HashMap<ClauseEprQuantifiedLiteral, Set<Integer>>();
			positions = new HashSet<Integer>();
			clToPos.put(ceql, positions);
			mVariableToClauseLitToPositions.put(tv, clToPos);
		} else {
			positions = clToPos.get(ceql);
		}
			
		positions.add(pos);
	}
}
