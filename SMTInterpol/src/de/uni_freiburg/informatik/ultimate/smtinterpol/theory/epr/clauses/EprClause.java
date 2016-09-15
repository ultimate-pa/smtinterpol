package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawgSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackPropagatedLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.IEprLiteral;

/**
 * Represents a clause that is only known to the EprTheory.
 * This means that the clause contains at least one free 
 * (implicitly forall-quantified) variable.
 * 
 * @author Alexander Nutz
 */
public class EprClause {
	

	private final Set<Literal> mDpllLiterals;
	private final EprTheory mEprTheory;
	private final DawgFactory<ApplicationTerm, TermVariable> mDawgFactory;

	private final Set<ClauseLiteral> mLiterals;

//	/**
//	 * Stores for every variable that occurs in the clause for each literal in the
//	 * clause at which position the variable occurs in the literal's atom (if at all).
//	 * This should be the only place where we need to speak about TermVariables..
//	 */
//	private final Map<TermVariable, Map<ClauseEprQuantifiedLiteral, Set<Integer>>> mVariableToClauseLitToPositions;
	
	/**
	 * Stores the variables occurring in this clause in the order determined by the HashMap mVariableToClauseLitToPositions
	 */
//	private final List<TermVariable> mVariables;
	private SortedSet<TermVariable> mVariables;
//	TermVariable[] mVariables;

	/**
	 * If this flag is true, the value of mEprClauseState can be relied on.
	 * Otherwise the state must be recomputed.
	 */
	private boolean mClauseStateIsDirty = true;

	/**
	 * The current fulfillment state of this epr clause
	 */
	private EprClauseState mEprClauseState;
	
	private Set<ClauseLiteral> mConflictLiterals;
	private IDawg<ApplicationTerm, TermVariable> mConflictPoints;
	
	/**
	 * track for a quantified clause literal that is a unit literal in some of the groundings of this clause,
	 *  which groundings those are
	 *  (note that we don't need to deal with unquantified eprPredicates here, because if one of them is unit,
	 *   then always all groundings of this clause are unit)
	 */
	private Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> mClauseLitToUnitPoints;
	

	public EprClause(Set<Literal> lits, EprTheory eprTheory) {
		mDpllLiterals = lits;
		mEprTheory = eprTheory;
		mDawgFactory = eprTheory.getDawgFactory();

		// set up the clause..

//		Pair<Map<TermVariable, Map<ClauseEprQuantifiedLiteral, Set<Integer>>>, Set<ClauseLiteral>> resPair = 
		Pair<SortedSet<TermVariable>, Set<ClauseLiteral>> resPair = 
				 createClauseLiterals(lits);

//		mVariableToClauseLitToPositions = Collections.unmodifiableMap(resPair.first);
		mLiterals = Collections.unmodifiableSet(resPair.second);

//		Set<TermVariable> keySet = mVariableToClauseLitToPositions.keySet();
////		mVariables = keySet.toArray(new TermVariable[keySet.size()]);
//		TreeSet<TermVariable> vars = new TreeSet<TermVariable>(EprHelpers.getColumnNamesComparator());
//		vars.addAll(keySet);
		mVariables = Collections.unmodifiableSortedSet(resPair.first);
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
	 * @return 
	 * @return 
	 */
//	private Pair<
//				Map<TermVariable, Map<ClauseEprQuantifiedLiteral, Set<Integer>>>, 
//				Set<ClauseLiteral>
//				> createClauseLiterals(Set<Literal> lits) {
	private Pair<SortedSet<TermVariable>, Set<ClauseLiteral>> createClauseLiterals(Set<Literal> lits) {

//		HashMap<TermVariable, Map<ClauseEprQuantifiedLiteral, Set<Integer>>> variableToClauseLitToPositions = 
//				new HashMap<TermVariable, Map<ClauseEprQuantifiedLiteral,Set<Integer>>>();
		SortedSet<TermVariable> variables = new TreeSet<TermVariable>(EprHelpers.getColumnNamesComparator());
		HashSet<ClauseLiteral> literals = new HashSet<ClauseLiteral>();

		Set<EprQuantifiedEqualityAtom> quantifiedEqualities = new HashSet<EprQuantifiedEqualityAtom>();

		for (Literal l : lits) {
			boolean polarity = l.getSign() == 1;
			DPLLAtom atom = l.getAtom();
			
			if (atom instanceof EprQuantifiedPredicateAtom) {
				EprQuantifiedPredicateAtom eqpa = (EprQuantifiedPredicateAtom) atom;
				
				variables.addAll(
						Arrays.asList(
								atom.getSMTFormula(mEprTheory.getTheory()).getFreeVars()));

				ClauseEprQuantifiedLiteral newL = new ClauseEprQuantifiedLiteral(
						polarity, eqpa, this, mEprTheory);
				literals.add(newL);
				eqpa.getEprPredicate().addQuantifiedOccurence(newL, this);
				
				
				continue;
			} else if (atom instanceof EprGroundPredicateAtom) {
				EprGroundPredicateAtom egpa = (EprGroundPredicateAtom) atom;
				ClauseEprGroundLiteral newL = new ClauseEprGroundLiteral(
						polarity, egpa, this, mEprTheory);
				literals.add(newL);
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
				literals.add(
						new ClauseDpllLiteral(polarity, atom, this, mEprTheory));
				continue;
			}
		}
		
		for (ClauseLiteral cl : literals) {
			if (cl instanceof ClauseEprQuantifiedLiteral) {
				ClauseEprQuantifiedLiteral ceql = (ClauseEprQuantifiedLiteral) cl;
				// update all quantified predicate atoms according to the quantified equalities
				// by excluding the corresponding points in their dawgs
				ceql.addExceptions(quantifiedEqualities);

//				// update the tracking of variable identities between quantified clause literals
//				ceql.updateIdenticalVariablePositions();
			}
		}
		
		assert literals.size() == mDpllLiterals.size() - quantifiedEqualities.size();
		
//		return new Pair<Map<TermVariable, Map<ClauseEprQuantifiedLiteral,Set<Integer>>>, Set<ClauseLiteral>>(
//				variableToClauseLitToPositions, literals);
		return new Pair<SortedSet<TermVariable>, Set<ClauseLiteral>>(
				variables, literals);

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
	 * Update the necessary data structure that help the clause to determine which state it is in.
	 *  --> determineState does not work correctly if this has not been called before.
	 * @param dsl
	 * @param literalsWithSamePredicate
	 * @return
	 */
	public void updateStateWrtDecideStackLiteral(IEprLiteral dsl, 
			Set<ClauseEprLiteral> literalsWithSamePredicate) {
		
		mClauseStateIsDirty = true;

		// update the storage of each clause literal that contains the decide stack literals
		// the clause literal is affected by
		for (ClauseEprLiteral cel : literalsWithSamePredicate) {
			assert cel.getClause() == this;
			
			if (cel.isDisjointFrom(dsl.getDawg())) {
				continue;
			}
			
			if (cel.getPolarity() == dsl.getPolarity()) {
				cel.addPartiallyFulfillingDecideStackLiteral(dsl);
			} else {
				cel.addPartiallyConflictingDecideStackLiteral(dsl);
			}
		}
	}


	public void backtrackStateWrtDecideStackLiteral(DecideStackLiteral dsl) {
		mClauseStateIsDirty = true;
		assert false : "TODO: implement";
	}

	/**
	 * This clause is informed that the DPLLEngine has set literal.
	 * The fulfillmentState of this clause may have to be updated because of this.
	 * 
	 * @param literal ground Epr Literal that has been set by DPLLEngine
	 * @return 
	 */
	public EprClauseState updateStateWrtDpllLiteral(Literal literal) {
		mClauseStateIsDirty = true;
		return determineClauseState();
	}

	public void backtrackStateWrtDpllLiteral(Literal literal) {
		mClauseStateIsDirty = true;
		assert false : "TODO: implement";
	}
	
//	public Map<ClauseEprQuantifiedLiteral, Set<Integer>> getClauseLitToPositions(TermVariable tv) {
//		return mVariableToClauseLitToPositions.get(tv);
//	}
	
//	void updateVariableToClauseLitToPosition(TermVariable tv, ClauseEprQuantifiedLiteral ceql, Integer pos) {
//		Map<ClauseEprQuantifiedLiteral, Set<Integer>> clToPos = mVariableToClauseLitToPositions.get(tv);
//		Set<Integer> positions = null;
//
//		if (clToPos == null) {
//			clToPos = new HashMap<ClauseEprQuantifiedLiteral, Set<Integer>>();
//			positions = new HashSet<Integer>();
//			clToPos.put(ceql, positions);
//			mVariableToClauseLitToPositions.put(tv, clToPos);
//		} else {
//			positions = clToPos.get(ceql);
//		}
//			
//		positions.add(pos);
//	}

	/**
	 * Checks if, in the current decide state, this EprClause is
	 *  a) a conflict clause or
	 *  b) a unit clause
	 * .. on at least one grounding.
	 * 
	 * TODO: this is a rather naive implementation
	 *   --> can we do something similar to two-watchers??
	 *   --> other plan: having a multi-valued dawg that count how many literals are fulfillable
	 *       for each point
	 * 
	 * @return a) something that characterized the conflict (TODO: what excactly?) or 
	 *         b) a unit literal for propagation (may be ground or not)
	 *         null if it is neither
	 */
	private EprClauseState determineClauseState() {
		
		// do we have a literal that is fulfilled (on all points)?
		for (ClauseLiteral cl : mLiterals) {
			if (cl.isFulfilled()) {
				mClauseStateIsDirty = false;
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
//				pointsToConsider.removeAllWithSubsetSignature(clFulfilledPoints);
				pointsToConsider.removeAll(clFulfilledPoints);
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

		Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> clauseLitToPotentialUnitPoints =
				new HashMap<ClauseLiteral, IDawg<ApplicationTerm,TermVariable>>();
		
		
		for (ClauseLiteral cl : mLiterals) {
			if (cl.isFulfillable()) {
				// at least one point of cl is still undecided (we sorted out fulfilled points before..)
				
//				Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> newClauseLitToPotentialUnitPoints =
//						new HashMap<ClauseLiteral, IDawg<ApplicationTerm,TermVariable>>();
				
					
				if (cl instanceof ClauseEprQuantifiedLiteral) {
					IDawg<ApplicationTerm, TermVariable> fp = ((ClauseEprQuantifiedLiteral) cl).getFulfillablePoints();
					
//					// some points may not be unit anymore because of this cl
//					for (Entry<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> en 
//							: clauseLitToPotentialUnitPoints.entrySet()) {
//						IDawg<ApplicationTerm, TermVariable> join = mDawgFactory.join(en.getValue(), fp);
//						if (! join.isEmpty()) {
//							newClauseLitToPotentialUnitPoints.put(en.getKey(), join);
//						}
//					}
//					clauseLitToPotentialUnitPoints = newClauseLitToPotentialUnitPoints;
					
//					IDawg<ApplicationTerm, TermVariable> fpOne = //pointsWhereOneLiteralIsFulfillable.intersect(fp);
//							mDawgFactory.addAllWithSubsetSignature(pointsWhereOneLiteralIsFulfillable, fp);
////							mDawgFactory.join(pointsWhereOneLiteralIsFulfillable, fp);
//					IDawg<ApplicationTerm, TermVariable> fpNo = //pointsWhereNoLiteralsAreFulfillable.intersect(fp);
//							mDawgFactory.addAllWithSubsetSignature(pointsWhereNoLiteralsAreFulfillable, fp);
////							mDawgFactory.join(pointsWhereOneLiteralIsFulfillable, fp);
					
					// transfer the fulfillable points from the clause literal signature to the dawg signature
//					IDawg<ApplicationTerm, TermVariable> fpClauseSig = 
//							mDawgFactory.addAllWithSubsetSignature(mDawgFactory.createEmptyDawg(mVariables), fp);
					
//					assert EprHelpers.haveSameSignature(fp, fpOne, fpNo, pointsWhereNoLiteralsAreFulfillable);
//					assert EprHelpers.haveSameSignature(fp, fpClauseSig, pointsWhereNoLiteralsAreFulfillable);
					
					IDawg<ApplicationTerm, TermVariable> toMoveFromNoToOne = pointsWhereNoLiteralsAreFulfillable.intersect(fp);
					IDawg<ApplicationTerm, TermVariable> toMoveFromOneToTwo = pointsWhereOneLiteralIsFulfillable.intersect(fp);

					assert EprHelpers.haveSameSignature(toMoveFromNoToOne, toMoveFromOneToTwo, pointsWhereNoLiteralsAreFulfillable);

					pointsWhereNoLiteralsAreFulfillable.removeAll(toMoveFromNoToOne);
					pointsWhereOneLiteralIsFulfillable.addAll(toMoveFromNoToOne);
					pointsWhereOneLiteralIsFulfillable.removeAll(toMoveFromOneToTwo);
					pointsWhereTwoOrMoreLiteralsAreFulfillable.addAll(toMoveFromOneToTwo);
//						pointsWhereTwoOrMoreLiteralsAreFulfillable.addAll(fpOne);
//					pointsWhereOneLiteralIsFulfillable.removeAll(fpOne);
//					pointsWhereOneLiteralIsFulfillable.addAll(fpNo);
//					pointsWhereNoLiteralsAreFulfillable.removeAll(fpNo);
//					
					// if the current ClauseLiteral is the last ClauseLiteral, its unit points are exactly the ones that 
					// moved from noFulfillableLiteral to OneFulfillableLiteral ..
					clauseLitToPotentialUnitPoints.put((ClauseEprQuantifiedLiteral) cl, 
							mDawgFactory.copyDawg(toMoveFromNoToOne));
					// ... however if we later find out for some of these points, that it is fulfilled somewhere else, we 
					// have to remove it from the list.
					for (Entry<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> en 
							: clauseLitToPotentialUnitPoints.entrySet()) {				
						en.getValue().removeAll(toMoveFromOneToTwo);
					}
				} else {
//					clauseLitToPotentialUnitPoints.clear();

//					// we need to do the intersection over all former possible unit points, right?
//					IDawg<ApplicationTerm, TermVariable> inter = mDawgFactory.createFullDawg(mVariables);
//					for (Entry<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> en 
//							: clauseLitToPotentialUnitPoints.entrySet()) {
//						// the current cl does not care about groundings, so the join remains unchanged
//						inter = inter.intersect(en.getValue());
//					}
//					if (! inter.isEmpty()) {
//							newClauseLitToPotentialUnitPoints.put(cl, inter);
//					}
//					clauseLitToPotentialUnitPoints = newClauseLitToPotentialUnitPoints;

					// the dawg of the current cl is the full dawg --> intersecting something with the full dawg means copying the something..
					IDawg<ApplicationTerm, TermVariable> toMoveFromNoToOne = mDawgFactory.copyDawg(pointsWhereNoLiteralsAreFulfillable);
					IDawg<ApplicationTerm, TermVariable> toMoveFromOneToTwo = mDawgFactory.copyDawg(pointsWhereOneLiteralIsFulfillable);

					assert EprHelpers.haveSameSignature(toMoveFromNoToOne, toMoveFromOneToTwo, pointsWhereNoLiteralsAreFulfillable);

					pointsWhereNoLiteralsAreFulfillable.removeAll(toMoveFromNoToOne);
					pointsWhereOneLiteralIsFulfillable.addAll(toMoveFromNoToOne);
					pointsWhereOneLiteralIsFulfillable.removeAll(toMoveFromOneToTwo);
					pointsWhereTwoOrMoreLiteralsAreFulfillable.addAll(toMoveFromOneToTwo);
				
//					pointsWhereTwoOrMoreLiteralsAreFulfillable.addAll(pointsWhereOneLiteralIsFulfillable);
//					pointsWhereOneLiteralIsFulfillable = 
//							mEprTheory.getDawgFactory().createEmptyDawg(mVariables);
//					pointsWhereOneLiteralIsFulfillable.addAll(pointsWhereNoLiteralsAreFulfillable);
//					pointsWhereNoLiteralsAreFulfillable =
//							mEprTheory.getDawgFactory().createEmptyDawg(mVariables);
//					
//					clauseLitToPotentialUnitPoints.put(cl, mDawgFactory.createFullDawg(mVariables));

					// if the current ClauseLiteral is the last ClauseLiteral, its unit points are exactly the ones that 
					// moved from noFulfillableLiteral to OneFulfillableLiteral ..
					clauseLitToPotentialUnitPoints.put((ClauseEprQuantifiedLiteral) cl, 
							mDawgFactory.copyDawg(toMoveFromNoToOne));
					// ... however if we later find out for some of these points, that it is fulfilled somewhere else, we 
					// have to remove it from the list.
					for (Entry<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> en 
							: clauseLitToPotentialUnitPoints.entrySet()) {				
						en.getValue().removeAll(toMoveFromOneToTwo);
					}
				}
			} else {
				assert cl.isRefuted();
			}
		}
		
		//remove all empty dawgs from clauseLitToPotentialUnitPoints
		Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> finalClauseLitToUnitPoints =
						new HashMap<ClauseLiteral, IDawg<ApplicationTerm,TermVariable>>();
		for (Entry<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> en : clauseLitToPotentialUnitPoints.entrySet()) {
			if (!en.getValue().isEmpty()) {
				finalClauseLitToUnitPoints.put(en.getKey(), en.getValue());
			}
		}


		if (!pointsWhereNoLiteralsAreFulfillable.isEmpty()) {
			mConflictPoints = pointsWhereNoLiteralsAreFulfillable;
			mEprClauseState = EprClauseState.Conflict;
		} else if (!pointsWhereOneLiteralIsFulfillable.isEmpty()) {
			mClauseLitToUnitPoints = finalClauseLitToUnitPoints;
			mEprClauseState = EprClauseState.Unit;
		} else {
			assert pointsWhereTwoOrMoreLiteralsAreFulfillable.supSetEq(pointsToConsider) 
				&& pointsToConsider.supSetEq(pointsWhereTwoOrMoreLiteralsAreFulfillable)
					: "we found no conflict and no unit points, thus all non-fulfilled points must be fulfillable "
					+ "on two or more literals";
			mEprClauseState = EprClauseState.Normal;
		}
		mClauseStateIsDirty = false;
		return mEprClauseState;
	}
	
	public SortedSet<TermVariable> getVariables() {
		return mVariables;
	}
	
	public EprClauseState getClauseState() {
		if (mClauseStateIsDirty)
			return determineClauseState();
		return mEprClauseState;
	}
	
	/**
	 * If this clause's state is Unit (i.e., if it is unit on at least one grounding), then this map
	 * stores which literal is unit on which groundings.
	 */
	public Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> getClauseLitToUnitPoints() {
		return mClauseLitToUnitPoints;
	}
	
//	public DecideStackPropagatedLiteral getUnitPropagationLiteral() {
//		assert isUnit() : "this may only be called on unit clauses";
//		assert false : "TODO: implement";
//		return null;
//	}

	public boolean isUnit() {
		if (mClauseStateIsDirty)
			return determineClauseState() == EprClauseState.Unit;
		return mEprClauseState == EprClauseState.Unit;
	}

	public boolean isConflict() {
		if (mClauseStateIsDirty)
			return determineClauseState() == EprClauseState.Conflict;
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
		assert !mClauseStateIsDirty;
		assert isConflict();
		assert mConflictLiterals != null : "this should have been set somewhere..";
		return mConflictLiterals;
	}
	
	public IDawg<ApplicationTerm, TermVariable> getConflictPoints() {
		assert !mClauseStateIsDirty;
		assert isConflict();
		assert mConflictPoints != null : "this should have been set somewhere..";
		return mConflictPoints;
	}

	public Set<ClauseLiteral> getLiterals() {
		return mLiterals;
	}
	
	public List<Literal[]> computeAllGroundings(List<TTSubstitution> allInstantiations) {
		ArrayList<Literal[]> result = new ArrayList<Literal[]>();
		for (TTSubstitution sub : allInstantiations) {
			ArrayList<Literal> groundInstList = getSubstitutedLiterals(sub);
			result.add(groundInstList.toArray(new Literal[groundInstList.size()]));
		}
		
		return result;
	}

	public List<Literal[]> computeAllGroundings(HashSet<ApplicationTerm> constants) {
		
		List<TTSubstitution> allInstantiations =  
				EprHelpers.getAllInstantiations(getVariables(), constants);
		
		return computeAllGroundings(allInstantiations);
	}
	
	protected ArrayList<Literal> getSubstitutedLiterals(TTSubstitution sub) {
		//		ArrayList<Literal> newLits = new ArrayList<Literal>();
		//		newLits.addAll(Arrays.asList(groundLiterals));
		//		for (Literal l : eprQuantifiedEqualityAtoms) {
		//			newLits.add(EprHelpers.applySubstitution(sub, l, mEprTheory));
		//		}
		//		for (Literal l : eprQuantifiedPredicateLiterals) {
		//			newLits.add(EprHelpers.applySubstitution(sub, l, mEprTheory));
		//		}
		//		return newLits;
		assert false : "TODO reimplement";
		return null;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("{");
		String comma = "";
		
		for (ClauseLiteral cl : getLiterals()) {
			sb.append(comma);
			sb.append(cl.toString());
			comma = ", ";
		}

		sb.append("}");
		return sb.toString();
	}


//	/**
//	 * Return a grounding of this clause that is a unit clause which allows to propagate the given literal.
//	 * @param literal a ground literal such that there exists a grounding of this clause 
//	 * 		that is a unit clause where the literal is the only non-refuted literal
//	 * @return a grounding of this clause that is a) unit b) has literal as its only fulfilling literal
//	 */
//	public Clause getUnitGrounding(Literal literal) {
//		DPLLAtom atom = literal.getAtom();
//
//		IDawg<ApplicationTerm, TermVariable> groundingDawg = null;
//		// find the matching clauseLiteral for the given literal (TODO: what if there are several?)
//		for (Entry<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> en : mClauseLitToUnitPoints.entrySet()) {
//			ClauseLiteral cl = en.getKey();
//			if (cl.getLiteral() == literal) {
//				// the literal is ground
//				assert literal.getAtom().getSMTFormula(mEprTheory.getTheory()).getFreeVars().length == 0;
//				groundingDawg = en.getValue();
//				break;
//			} else if (cl instanceof ClauseEprQuantifiedLiteral
//					&& atom instanceof EprPredicateAtom) {
//				EprPredicateAtom epa = (EprPredicateAtom) atom;
//				ClauseEprQuantifiedLiteral ceql = (ClauseEprQuantifiedLiteral) cl;
//
//				if (epa.getEprPredicate() != ceql.getEprPredicate()) {
//					continue;
//				}
//				Term[] ceqlArgs = ceql.mArgumentTerms.toArray(new Term[ceql.mArgumentTerms.size()]);
//				TTSubstitution unifier = epa.getArgumentsAsTermTuple().match(new TermTuple(ceqlArgs), mEprTheory.getEqualityManager());
//				if (unifier != null) {
//					groundingDawg = en.getValue();
//					break;
//				}
//			}
//		}
//		assert groundingDawg != null && ! groundingDawg.isEmpty();
//
//		//TODO: sample one point from the dawg, so we give a one-point dawg to getGroundings() ?..
//		
//		Set<Clause> groundings = getGroundings(groundingDawg);
//		
//		return groundings.iterator().next();
//	}


	public Set<Clause> getGroundings(IDawg<ApplicationTerm, TermVariable> groundingDawg) {
		assert groundingDawg.getColnames().equals(mVariables) : "signatures don't match";

		Set<Clause> result = new HashSet<Clause>();

		for (List<ApplicationTerm> point : groundingDawg){
			TTSubstitution sub = new TTSubstitution(groundingDawg.getColnames(), point);
			List<Literal> groundLits = new ArrayList<Literal>();
			for (ClauseLiteral cl : getLiterals()) {
				if (cl instanceof ClauseEprQuantifiedLiteral) {
					ClauseEprQuantifiedLiteral ceql = (ClauseEprQuantifiedLiteral) cl;
					Term[] ceqlArgs = ceql.mArgumentTerms.toArray(new Term[ceql.mArgumentTerms.size()]);
					TermTuple newTT = sub.apply(new TermTuple(ceqlArgs));
					assert newTT.getFreeVars().size() == 0;
					EprPredicateAtom at = ceql.getEprPredicate().getAtomForTermTuple(newTT, mEprTheory.getTheory(), 0); //TODO assertionstacklevel
					
					Literal newLit = cl.getPolarity() ? at : at.negate();

					groundLits.add(newLit);
				} else {
					groundLits.add(cl.getLiteral());
				}
			}
			
			result.add(new Clause(groundLits.toArray(new Literal[groundLits.size()])));
		}

		return result;
	}
}
