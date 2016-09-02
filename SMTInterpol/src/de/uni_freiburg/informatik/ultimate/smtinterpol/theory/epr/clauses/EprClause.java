package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawgSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackPropagatedLiteral;

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
	final DawgFactory<ApplicationTerm, TermVariable> mDawgFactory;

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
	List<TermVariable> mVariables;
//	SortedSet<TermVariable> mVariables;
//	TermVariable[] mVariables;

	/*
	 * The following two fields are only used during creation of the clause.
	 */
	HashMap<TermVariable, Map<ClauseEprQuantifiedLiteral, Set<Integer>>> mVariableToClauseLitToPositionsTemp;
	Set<ClauseLiteral> mLiteralsTemp;
	private EprClauseState mEprClauseState;
	private Set<ClauseLiteral> mConflictLiterals;
	private IDawg<ApplicationTerm, TermVariable> mConflictPoints;
	private Map<ClauseEprQuantifiedLiteral, IDawg<ApplicationTerm, TermVariable>> mClauseLitToUnitPoints;
	

	public EprClause(Set<Literal> lits, EprTheory eprTheory) {
		mDpllLiterals = lits;
		mEprTheory = eprTheory;
		mDawgFactory = eprTheory.getDawgFactory();

		// set up the clause..

		mVariableToClauseLitToPositionsTemp = new HashMap<TermVariable, Map<ClauseEprQuantifiedLiteral,Set<Integer>>>();
		mLiteralsTemp = new HashSet<ClauseLiteral>();

		createClauseLiterals(lits);

		mLiterals = Collections.unmodifiableSet(mLiteralsTemp);
		mVariableToClauseLitToPositions = Collections.unmodifiableMap(mVariableToClauseLitToPositionsTemp);

		Set<TermVariable> keySet = mVariableToClauseLitToPositions.keySet();
//		mVariables = keySet.toArray(new TermVariable[keySet.size()]);
//		mVariables = new TreeSet<TermVariable>(eprTheory.getTermVariableComparator());
//		mVariables.addAll(keySet);
		mVariables = new ArrayList<TermVariable>(keySet);

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
	 * @param literalsWithSamePredicate
	 * @return
	 */
	public EprClauseState updateStateWrtDecideStackLiteral(DecideStackLiteral dsl, 
			Set<ClauseEprQuantifiedLiteral> literalsWithSamePredicate) {

		for (ClauseEprQuantifiedLiteral ceql : literalsWithSamePredicate) {
			assert ceql.getClause() == this;
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
	
	void updateVariableToClauseLitToPosition(TermVariable tv, ClauseEprQuantifiedLiteral ceql, Integer pos) {
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
		
		// do we have a literal that is fulfilled (on all points)?
		for (ClauseLiteral cl : mLiterals) {
			if (cl.isFulfilled()) {
				return EprClauseState.Fulfilled;
			}
		}
		
		// Although the whole literal is not fulfilled, some points may be..
		// we only need to consider points where no literal is decided "true" yet..
		IDawg<ApplicationTerm, TermVariable> pointsToConsider = 
				mEprTheory.getDawgFactory().createFullDawg(mVariables);
		for (ClauseLiteral cl : mLiterals) {
			if (cl.isRefuted()) {
				continue;
			}

			if (cl instanceof ClauseEprQuantifiedLiteral) {
				IDawg<ApplicationTerm, TermVariable> clFulfilledPoints = 
						((ClauseEprQuantifiedLiteral) cl).getFulfilledPoints();
				pointsToConsider.removeAllWithSubsetSignature(clFulfilledPoints);
			}
		}
		
		
		/**
		 * The set of all points (over this clause's signature, read: groundings) where no literal of this 
		 * clause is fulfillable
		 *  --> once the computation is complete, this represents the set of groundings that are a conflict.
		 */
		IDawg<ApplicationTerm, TermVariable> pointsWhereNoLiteralsAreFulfillable =
				mDawgFactory.copyDawg(pointsToConsider);
		IDawg<ApplicationTerm, TermVariable> pointsWhereOneLiteralIsFulfillable =
				mDawgFactory.createEmptyDawg(mVariables);
		IDawg<ApplicationTerm, TermVariable> pointsWhereTwoOrMoreLiteralsAreFulfillable =
				mDawgFactory.createEmptyDawg(mVariables);
		assert EprHelpers.haveSameSignature(pointsWhereNoLiteralsAreFulfillable,
				pointsWhereOneLiteralIsFulfillable,
				pointsWhereTwoOrMoreLiteralsAreFulfillable);

		Map<ClauseEprQuantifiedLiteral, IDawg<ApplicationTerm, TermVariable>> clauseLitToPotentialUnitPoints =
				new HashMap<ClauseEprQuantifiedLiteral, IDawg<ApplicationTerm,TermVariable>>();
		
		
		for (ClauseLiteral cl : mLiterals) {
			if (cl.isFulfillable()) {
				// at leat one point of cl is still undecided (we sorted out fulfilled points before..)
				
				Map<ClauseEprQuantifiedLiteral, IDawg<ApplicationTerm, TermVariable>> newClauseLitToPotentialUnitPoints =
						new HashMap<ClauseEprQuantifiedLiteral, IDawg<ApplicationTerm,TermVariable>>();
				
					
				if (cl instanceof ClauseEprQuantifiedLiteral) {
					IDawg<ApplicationTerm, TermVariable> fp = ((ClauseEprQuantifiedLiteral) cl).getFulfillablePoints();
					
					// some points may not be unit anymore because of this cl
					for (Entry<ClauseEprQuantifiedLiteral, IDawg<ApplicationTerm, TermVariable>> en 
							: clauseLitToPotentialUnitPoints.entrySet()) {
						IDawg<ApplicationTerm, TermVariable> join = mDawgFactory.join(en.getValue(), fp);
						if (! join.isEmpty()) {
							newClauseLitToPotentialUnitPoints.put(en.getKey(), join);
						}
					}
					clauseLitToPotentialUnitPoints = newClauseLitToPotentialUnitPoints;
					
					IDawg<ApplicationTerm, TermVariable> fpOne = //pointsWhereOneLiteralIsFulfillable.intersect(fp);
							mDawgFactory.join(pointsWhereOneLiteralIsFulfillable, fp);
					IDawg<ApplicationTerm, TermVariable> fpNo = //pointsWhereNoLiteralsAreFulfillable.intersect(fp);
							mDawgFactory.join(pointsWhereOneLiteralIsFulfillable, fp);
					
					assert EprHelpers.haveSameSignature(fp, fpOne, fpNo, pointsWhereNoLiteralsAreFulfillable);
					
					pointsWhereTwoOrMoreLiteralsAreFulfillable.addAll(fpOne);
					pointsWhereOneLiteralIsFulfillable.removeAll(fpOne);
					pointsWhereOneLiteralIsFulfillable.addAll(fpNo);
					pointsWhereNoLiteralsAreFulfillable.removeAll(fpNo);
					
					clauseLitToPotentialUnitPoints.put((ClauseEprQuantifiedLiteral) cl, 
							mDawgFactory.copyDawg(pointsWhereOneLiteralIsFulfillable));
				} else {
					clauseLitToPotentialUnitPoints.clear();
					
					pointsWhereTwoOrMoreLiteralsAreFulfillable.addAll(pointsWhereOneLiteralIsFulfillable);
					pointsWhereOneLiteralIsFulfillable = 
							mEprTheory.getDawgFactory().createEmptyDawg(mVariables);
					pointsWhereOneLiteralIsFulfillable.addAll(pointsWhereNoLiteralsAreFulfillable);
					pointsWhereNoLiteralsAreFulfillable =
							mEprTheory.getDawgFactory().createEmptyDawg(mVariables);
					
//					clauseLitToPotentialUnitPoints.put(cl, mDawgFactory.createFullDawg(mVariables));
				}
			} else {
				assert cl.isRefuted();
			}
		}
		
		if (!pointsWhereNoLiteralsAreFulfillable.isEmpty()) {
			mConflictPoints = pointsWhereNoLiteralsAreFulfillable;
			return EprClauseState.Conflict;
		} else if (!pointsWhereOneLiteralIsFulfillable.isEmpty()) {
			mClauseLitToUnitPoints = clauseLitToPotentialUnitPoints;
			return EprClauseState.Unit;
		} else {
			assert pointsWhereTwoOrMoreLiteralsAreFulfillable.isUniversal();
			return EprClauseState.Normal;
		}
	}
	
//	public TermVariable[] getVariables() {
//	public SortedSet<TermVariable> getVariables() {
	public Collection<TermVariable> getVariables() {
		return mVariables;
	}
	
	public EprClauseState getClauseState() {
		return mEprClauseState;
	}
	
	/**
	 * If this clause's state is Unit (i.e., if it is unit on at least one grounding), then this map
	 * stores which literal is unit on which groundings.
	 */
	public Map<ClauseEprQuantifiedLiteral, IDawg<ApplicationTerm, TermVariable>> getClauseLitToUnitPoints() {
		assert getClauseState() == EprClauseState.Unit;
		return mClauseLitToUnitPoints;
	}
	
	public DecideStackPropagatedLiteral getUnitPropagationLiteral() {
		assert isUnit() : "this may only be called on unit clauses";
		assert false : "TODO: implement";
		return null;
	}

	public boolean isUnit() {
		return mEprClauseState == EprClauseState.Unit;
	}

	public boolean isConflict() {
		// TODO Auto-generated method stub
		return mEprClauseState == EprClauseState.Conflict;
	}

	public Set<ClauseLiteral> getLiteralsWithEprPred(EprPredicate eprPred) {
		Set<ClauseLiteral> result = new HashSet<ClauseLiteral>();
		for (ClauseLiteral cl : mLiterals) {
			if (cl instanceof ClauseEprLiteral
					&& ((ClauseEprLiteral)cl).getEprPredicate() == eprPred) {
				result.add(cl);
			}
		}
		return result;
	}
	
	/**
	 * Returns the literal(s) that were made unfulfillable when this clause became a conflict.
	 * @return
	 */
	public Set<ClauseLiteral> getConflictLiterals() {
		assert isConflict();
		assert mConflictLiterals != null : "this should have been set somewhere..";
		return mConflictLiterals;
	}
	
	public IDawg<ApplicationTerm, TermVariable> getConflictPoints() {
		assert isConflict();
		assert mConflictPoints != null : "this should have been set somewhere..";
		return mConflictPoints;
	}

	public Set<ClauseLiteral> getLiterals() {
		return mLiterals;
	}
}
