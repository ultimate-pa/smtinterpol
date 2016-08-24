package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;

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
	 * This should be the only place where we need to speak about TermVariables..
	 */
	final Map<TermVariable, Map<ClauseEprQuantifiedLiteral, Set<Integer>>> mVariableToClauseLitToPositions;
	
	/**
	 * Stores the variabels occuring in this clause in the order determined by the HashMap mVariableToClauseLitToPositions
	 */
	TermVariable[] mVariables;

	/*
	 * The following two fields are only used during creation of the clause.
	 */
	HashMap<TermVariable, Map<ClauseEprQuantifiedLiteral, Set<Integer>>> mVariableToClauseLitToPositionsTemp;
	Set<ClauseLiteral> mLiteralsTemp;
	private EprClauseState mEprClauseState;

	public EprClause(Set<Literal> lits, EprTheory eprTheory) {
		mDpllLiterals = lits;
		mEprTheory = eprTheory;

		// set up the clause..

		mVariableToClauseLitToPositionsTemp = new HashMap<TermVariable, Map<ClauseEprQuantifiedLiteral,Set<Integer>>>();
		mLiteralsTemp = new HashSet<ClauseLiteral>();

		createClauseLiterals(lits);

		mLiterals = Collections.unmodifiableSet(mLiteralsTemp);
		mVariableToClauseLitToPositions = Collections.unmodifiableMap(mVariableToClauseLitToPositionsTemp);

		Set<TermVariable> keySet = mVariableToClauseLitToPositions.keySet();
		mVariables = keySet.toArray(new TermVariable[keySet.size()]);

		// those ..Temp fields should not be used afterwards..
		mLiteralsTemp = null;
		mVariableToClauseLitToPositionsTemp = null;
	}

	/**
	 * Set up the clause in terms of our Epr data structures.
	 * Fills the fields mVariableToClauseLitPositionsTemp and mLiteralsTemp.
	 * 
	 * TODOs:
	 *  - detect tautologies
	 *  - detect duplicate literals
	 * 
	 * @param lits The (DPLL) literals that this clause is created from.
	 */
	private void createClauseLiterals(Set<Literal> lits) {
		
		Set<EprQuantifiedEqualityAtom> quantifiedEqualities = new HashSet<EprQuantifiedEqualityAtom>();

		for (Literal l : lits) {
			boolean polarity = l.getSign() == 1;
			DPLLAtom atom = l.getAtom();
			
			if (atom instanceof EprQuantifiedPredicateAtom) {
				EprQuantifiedPredicateAtom eqpa = (EprQuantifiedPredicateAtom) atom;

				ClauseEprQuantifiedLiteral newL = new ClauseEprQuantifiedLiteral(
						polarity, eqpa, this, mEprTheory);
				mLiteralsTemp.add(newL);
				eqpa.getEprPredicate().addQuantifiedOccurence(newL, this);
				
				for (int i = 0; i < eqpa.getArguments().length; i++) {
					if (! (eqpa.getArguments()[i] instanceof TermVariable))
						continue;
					TermVariable tv = (TermVariable) eqpa.getArguments()[i];
					this.updateVariableToClauseLitToPosition(tv, newL, i);
				}			
				
				continue;
			} else if (atom instanceof EprGroundPredicateAtom) {
				EprGroundPredicateAtom egpa = (EprGroundPredicateAtom) atom;
				ClauseEprGroundLiteral newL = new ClauseEprGroundLiteral(
						polarity, egpa, this, mEprTheory);
				mLiteralsTemp.add(newL);
				egpa.getEprPredicate().addGroundOccurence(newL, this);
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
				mLiteralsTemp.add(
						new ClauseDpllLiteral(polarity, atom, this, mEprTheory));
				continue;
			}
		}
		
		for (ClauseLiteral cl : mLiteralsTemp) {
			if (cl instanceof ClauseEprQuantifiedLiteral) {
				ClauseEprQuantifiedLiteral ceql = (ClauseEprQuantifiedLiteral) cl;
				// update all quantified predicate atoms according to the quantified equalities
				// by excluding the corresponding points in their dawgs
				ceql.addExceptions(quantifiedEqualities);

				// update the tracking of variable identities between quantified clause literals
				ceql.updateIdenticalVariablePositions();
			}
		}
		
		assert mLiteralsTemp.size() == mDpllLiterals.size() - quantifiedEqualities.size();
	}
	
	/**
	 * Removes the traces of the clause in the data structures that link to it.
	 * The application I can think of now is a pop command.
	 */
	public void disposeOfClause() {
		for (ClauseLiteral cl : mLiterals) {
			if (cl instanceof ClauseEprQuantifiedLiteral) {
				ClauseEprQuantifiedLiteral ceql = (ClauseEprQuantifiedLiteral) cl;
//				ceql.getEprPredicate().removeQuantifiedOccurence(this, )
				ceql.getEprPredicate().notifyAboutClauseDisposal(this);
			}
		}
	}

	/**
	 * 
	 * @param dsl
	 * @param concernedLiterals
	 * @return
	 */
	public EprClauseState updateStateWrtDecideStackLiteral(DecideStackLiteral dsl, 
			Set<ClauseEprQuantifiedLiteral> concernedLiterals) {

		for (ClauseEprQuantifiedLiteral ceql : concernedLiterals) {
			if (ceql.getPolarity() == dsl.getPolarity()) {
				ceql.addPartiallyFulfillingDecideStackLiteral(dsl);
			} else {
				ceql.addPartiallyConflictingDecideStackLiteral(dsl);
			}
		}

		determineClauseState();
		return mEprClauseState;
	}

	public void backtrackStateWrtDecideStackLiteral(DecideStackLiteral dsl) {
		assert false : "TODO: implement";
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
	
	private void updateVariableToClauseLitToPosition(TermVariable tv, ClauseEprQuantifiedLiteral ceql, Integer pos) {
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

	/**
	 * Checks if, in the current decide state, this EprClause is
	 *  a) a conflict clause or
	 *  b) a unit clause
	 * .. on at least one grounding.
	 * 
	 * TODO: this is a rather naive implementation
	 *   --> can we do something similar to two-watchers??
	 * 
	 * @return a) something that characterized the conflict (TODO: what excactly?) or 
	 *         b) a unit literal for propagation (may be ground or not)
	 *         null if it is neither
	 */
	private EprClauseState determineClauseState() {
		
		IDawg pointsWhereNoLiteralsAreFulfillable =
				mEprTheory.getDawgFactory().createEmptyDawg(mVariables);
		IDawg pointsWhereOneLiteralIsFulfillable =
				mEprTheory.getDawgFactory().createEmptyDawg(mVariables);
		IDawg pointsWhereTwoOrMoreLiteralsAreFulfillable =
				mEprTheory.getDawgFactory().createEmptyDawg(mVariables);

		for (ClauseLiteral cl : mLiterals) {

			
			if (cl.isFulfilled()) {
				return EprClauseState.Fulfilled;
			}
			
			if (cl.isFulfillable()) {
				
				if (cl instanceof ClauseEprQuantifiedLiteral) {
					IDawg fp = ((ClauseEprQuantifiedLiteral) cl).getFulfillablePoints();
					
					IDawg fpOne = pointsWhereOneLiteralIsFulfillable.intersect(fp);
					IDawg fpNo = pointsWhereNoLiteralsAreFulfillable.intersect(fp);
					
					pointsWhereTwoOrMoreLiteralsAreFulfillable.addAll(fpOne);
					pointsWhereOneLiteralIsFulfillable.removeAll(fpOne);
					pointsWhereOneLiteralIsFulfillable.addAll(fpNo);
					pointsWhereNoLiteralsAreFulfillable.removeAll(fpNo);
					
				} else {
					pointsWhereTwoOrMoreLiteralsAreFulfillable.addAll(pointsWhereOneLiteralIsFulfillable);
					pointsWhereOneLiteralIsFulfillable = 
							mEprTheory.getDawgFactory().createEmptyDawg(mVariables);
					pointsWhereOneLiteralIsFulfillable.addAll(pointsWhereNoLiteralsAreFulfillable);
					pointsWhereNoLiteralsAreFulfillable =
							mEprTheory.getDawgFactory().createEmptyDawg(mVariables);
				}
			}
		}
		
		if (!pointsWhereNoLiteralsAreFulfillable.isEmpty()) {
			return EprClauseState.Conflict;
		} else if (!pointsWhereOneLiteralIsFulfillable.isEmpty()) {
			return EprClauseState.Unit;
		} else {
			assert pointsWhereTwoOrMoreLiteralsAreFulfillable.isUniversal();
			return EprClauseState.Normal;
		}
	}
	
	public TermVariable[] getVariables() {
		return mVariables;
	}
	
	public EprClauseState getClauseState() {
		return mEprClauseState;
	}
}
