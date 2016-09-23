package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackDecisionLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;
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
	private SortedSet<TermVariable> mVariables;

	/**
	 * If this flag is true, the value of mEprClauseState can be relied on.
	 * Otherwise the state must be recomputed.
	 */
	private boolean mClauseStateIsDirty = true;

	/**
	 * The current fulfillment state of this epr clause
	 */
	private EprClauseState mEprClauseState;
	
//	private Set<ClauseLiteral> mConflictLiterals;
	private IDawg<ApplicationTerm, TermVariable> mConflictPoints;
	
	/**
	 * track for a quantified clause literal that is a unit literal in some of the groundings of this clause,
	 *  which groundings those are
	 *  (note that we don't need to deal with unquantified eprPredicates here, because if one of them is unit,
	 *   then always all groundings of this clause are unit)
	 */
	private Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> mClauseLitToUnitPoints;
	
	private UnitPropagationData mUnitPropagationData;
	
	/*
	 * stuff relative to the decide stack border; done as maps now, but maybe one item each is enough??
	 */
	private Map<DecideStackLiteral, Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>>> mDecideStackBorderToClauseLitToUnitPoints =
			new HashMap<DecideStackLiteral, Map<ClauseLiteral,IDawg<ApplicationTerm,TermVariable>>>();
	private Map<DecideStackLiteral, EprClauseState> mDecideStackBorderToClauseState = 
			new HashMap<DecideStackLiteral, EprClauseState>();
	private Map<DecideStackLiteral, IDawg<ApplicationTerm, TermVariable>> mDecideStackBorderToConflictPoints =
			new HashMap<DecideStackLiteral, IDawg<ApplicationTerm,TermVariable>>();
	private Map<DecideStackLiteral, UnitPropagationData> mDecideStackBorderToUnitPropagationData;
	

	public EprClause(Set<Literal> lits, EprTheory eprTheory) {
		mDpllLiterals = lits;
		mEprTheory = eprTheory;
		mDawgFactory = eprTheory.getDawgFactory();

		// set up the clause..

		Pair<SortedSet<TermVariable>, Set<ClauseLiteral>> resPair = 
				 createClauseLiterals(lits);

		mLiterals = Collections.unmodifiableSet(resPair.second);

		mVariables = Collections.unmodifiableSortedSet(resPair.first);
		
		registerFulfillingOrConflictingEprLiteralInClauseLiterals();
	}


	private void registerFulfillingOrConflictingEprLiteralInClauseLiterals() {
		for (ClauseLiteral cl : getLiterals()) {
			if (!(cl instanceof ClauseEprLiteral)) {
				continue;
			}
			ClauseEprLiteral cel = (ClauseEprLiteral) cl;
			for (IEprLiteral dsl : cel.getEprPredicate().getEprLiterals()) {
				if (cel.isDisjointFrom(dsl.getDawg())) {
					continue;
				}
			
				if (dsl.getPolarity() == cel.getPolarity()) {
					cel.addPartiallyFulfillingEprLiteral(dsl);
				} else {
					cel.addPartiallyConflictingEprLiteral(dsl);
				}
			}	
		}
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
				cel.addPartiallyFulfillingEprLiteral(dsl);
			} else {
				cel.addPartiallyConflictingEprLiteral(dsl);
			}
		}
	}


	public void backtrackStateWrtDecideStackLiteral(DecideStackLiteral dsl) {
		mClauseStateIsDirty = true;
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
		return determineClauseState(null);
	}

	public void backtrackStateWrtDpllLiteral(Literal literal) {
		mClauseStateIsDirty = true;
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
	private EprClauseState determineClauseState(DecideStackLiteral decideStackBorder) {
		
		// do we have a literal that is fulfilled (on all points)?
		for (ClauseLiteral cl : getLiterals()) {
			if (cl.isFulfilled(decideStackBorder)) {
				setClauseState(decideStackBorder, EprClauseState.Fulfilled);
//				mClauseStateIsDirty = false;
//				mEprClauseState = EprClauseState.Fulfilled;
				return getClauseState(decideStackBorder);
			}
		}
		
		// Although the whole literal is not fulfilled, some points may be..
		// we only need to consider points where no literal is decided "true" yet..
		IDawg<ApplicationTerm, TermVariable> pointsToConsider = 
				mEprTheory.getDawgFactory().createFullDawg(getVariables());
		for (ClauseLiteral cl : getLiterals()) {
			if (cl.isRefuted(decideStackBorder)) {
				continue;
			}

			if (cl instanceof ClauseEprQuantifiedLiteral) {
				IDawg<ApplicationTerm, TermVariable> clFulfilledPoints = 
						((ClauseEprQuantifiedLiteral) cl).getFulfilledPoints();
//				pointsToConsider.removeAllWithSubsetSignature(clFulfilledPoints);
				pointsToConsider.removeAll(clFulfilledPoints);
			}
		}
		assert EprHelpers.verifySortsOfPoints(pointsToConsider, getVariables());
		
		
		/**
		 * The set of all points (over this clause's signature, read: groundings) where no literal of this 
		 * clause is fulfillable
		 *  --> once the computation is complete, this represents the set of groundings that are a conflict.
		 */
		IDawg<ApplicationTerm, TermVariable> pointsWhereNoLiteralsAreFulfillable =
				mDawgFactory.copyDawg(pointsToConsider);
		IDawg<ApplicationTerm, TermVariable> pointsWhereOneLiteralIsFulfillable =
				mDawgFactory.createEmptyDawg(getVariables());
		IDawg<ApplicationTerm, TermVariable> pointsWhereTwoOrMoreLiteralsAreFulfillable =
				mDawgFactory.createEmptyDawg(getVariables());
		assert EprHelpers.haveSameSignature(pointsWhereNoLiteralsAreFulfillable,
				pointsWhereOneLiteralIsFulfillable,
				pointsWhereTwoOrMoreLiteralsAreFulfillable);

		Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> clauseLitToPotentialUnitPoints =
				new HashMap<ClauseLiteral, IDawg<ApplicationTerm,TermVariable>>();
		
		
		for (ClauseLiteral cl : getLiterals()) {
			if (cl.isFulfillable(decideStackBorder)) {
				// at least one point of cl is still undecided (we sorted out fulfilled points before..)
				// we move the newly fulfillable points one up in our hierarchy
				
				IDawg<ApplicationTerm, TermVariable> toMoveFromNoToOne = null;
				IDawg<ApplicationTerm, TermVariable> toMoveFromOneToTwo = null;
				if (cl instanceof ClauseEprQuantifiedLiteral) {
					IDawg<ApplicationTerm, TermVariable> fp = 
							((ClauseEprQuantifiedLiteral) cl).getFulfillablePoints(decideStackBorder);

					toMoveFromNoToOne = pointsWhereNoLiteralsAreFulfillable.intersect(fp);
					toMoveFromOneToTwo = pointsWhereOneLiteralIsFulfillable.intersect(fp);
				} else {
					// the dawg of the current cl is the full dawg --> intersecting something with the full dawg means copying the something..
					toMoveFromNoToOne = mDawgFactory.copyDawg(pointsWhereNoLiteralsAreFulfillable);
					toMoveFromOneToTwo = mDawgFactory.copyDawg(pointsWhereOneLiteralIsFulfillable);
				}
				
				assert EprHelpers.haveSameSignature(toMoveFromNoToOne, toMoveFromOneToTwo, pointsWhereNoLiteralsAreFulfillable);

				pointsWhereNoLiteralsAreFulfillable.removeAll(toMoveFromNoToOne);
				pointsWhereOneLiteralIsFulfillable.addAll(toMoveFromNoToOne);
				pointsWhereOneLiteralIsFulfillable.removeAll(toMoveFromOneToTwo);
				pointsWhereTwoOrMoreLiteralsAreFulfillable.addAll(toMoveFromOneToTwo);
				
				// if the current ClauseLiteral is the last ClauseLiteral, its unit points are exactly the ones that 
				// moved from noFulfillableLiteral to OneFulfillableLiteral ..
				clauseLitToPotentialUnitPoints.put(cl, mDawgFactory.copyDawg(toMoveFromNoToOne));
				// ... however if we later find out for some of these points, that it is fulfilled somewhere else, we 
				// have to remove it from the list.
				for (Entry<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> en 
						: clauseLitToPotentialUnitPoints.entrySet()) {				
					en.getValue().removeAll(toMoveFromOneToTwo);
				}
			} else {
				assert cl.isRefuted(decideStackBorder);
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

		assert EprHelpers.verifySortsOfPoints(pointsWhereNoLiteralsAreFulfillable, getVariables());
		assert EprHelpers.verifySortsOfPoints(pointsWhereOneLiteralIsFulfillable, getVariables());
		assert EprHelpers.verifySortsOfPoints(pointsWhereTwoOrMoreLiteralsAreFulfillable, getVariables());


		if (!pointsWhereNoLiteralsAreFulfillable.isEmpty()) {
			setPointsWhereNoLiteralsAreFulfillable(decideStackBorder, pointsWhereNoLiteralsAreFulfillable);
			setClauseState(decideStackBorder, EprClauseState.Conflict);
		} else if (!pointsWhereOneLiteralIsFulfillable.isEmpty()) {
//			setClauseLitToUnitPoints(decideStackBorder, finalClauseLitToUnitPoints);
			UnitPropagationData upd = new UnitPropagationData(finalClauseLitToUnitPoints, mDawgFactory);
			setUnitPropagationData(decideStackBorder, upd);
			setClauseState(decideStackBorder, EprClauseState.Unit);
		} else {
			assert pointsWhereTwoOrMoreLiteralsAreFulfillable.supSetEq(pointsToConsider) 
				&& pointsToConsider.supSetEq(pointsWhereTwoOrMoreLiteralsAreFulfillable)
					: "we found no conflict and no unit points, thus all non-fulfilled points must be fulfillable "
					+ "on two or more literals";
			setClauseState(decideStackBorder, EprClauseState.Normal);
		}
		return getClauseState(decideStackBorder);
	}
	
	private void setUnitPropagationData(DecideStackLiteral decideStackBorder, UnitPropagationData upd) {
		if (decideStackBorder == null) {
			mUnitPropagationData = upd;
		} else { 
			mDecideStackBorderToUnitPropagationData.put(decideStackBorder, upd);
		}
	}


	private void setPointsWhereNoLiteralsAreFulfillable(DecideStackLiteral decideStackBorder,
		IDawg<ApplicationTerm, TermVariable> pointsWhereNoLiteralsAreFulfillable) {
		if (decideStackBorder == null) {
			mConflictPoints = pointsWhereNoLiteralsAreFulfillable;
		} else {
			mDecideStackBorderToConflictPoints.put(decideStackBorder, pointsWhereNoLiteralsAreFulfillable);
		}
}


//	private void setClauseLitToUnitPoints(
//			DecideStackLiteral decideStackBorder, 
//			Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> finalClauseLitToUnitPoints) {
//		if (decideStackBorder == null) {
//			mClauseLitToUnitPoints = finalClauseLitToUnitPoints;
//		} else {
//			mDecideStackBorderToClauseLitToUnitPoints.put(decideStackBorder, finalClauseLitToUnitPoints);
//			assert mDecideStackBorderToClauseLitToUnitPoints.size() < 10 : "if this is getting big, "
//					+ "we might want to throw old entries away? do we even need more than one?";
//		}
//	}


	private EprClauseState getClauseState(DecideStackLiteral decideStackBorder) {
		if (decideStackBorder == null) {
			return mEprClauseState;
		} else {
			EprClauseState res = mDecideStackBorderToClauseState.get(decideStackBorder);
			assert res != null;
			return res;
		}
	}


	private void setClauseState(DecideStackLiteral decideStackBorder, EprClauseState newState) {
		if (decideStackBorder == null) {
			mClauseStateIsDirty = false;
			mEprClauseState = newState;
		} else {
			mDecideStackBorderToClauseState.put(decideStackBorder, newState);
		}
	}


	public SortedSet<TermVariable> getVariables() {
		return mVariables;
	}
	
//	public EprClauseState getClauseState() {
//		if (mClauseStateIsDirty)
//			return determineClauseState(null);
//		return mEprClauseState;
//	}
	
	public UnitPropagationData getUnitPropagationData() {
		assert mUnitPropagationData != null;
		UnitPropagationData result = mUnitPropagationData;
		mUnitPropagationData = null;
		return result;
	}
	
//	/**
//	 * If this clause's state is Unit (i.e., if it is unit on at least one grounding), then this map
//	 * stores which literal is unit on which groundings.
//	 * Note that the dawg is in the clause's signature (not some predicate's)
//	 */
//	public Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> getClauseLitToUnitPoints() {
//		return mClauseLitToUnitPoints;
//	}
	
	public boolean isUnit() {
		if (mClauseStateIsDirty) {
			return determineClauseState(null) == EprClauseState.Unit;
		}
		return mEprClauseState == EprClauseState.Unit;
	}

	public boolean isConflict() {
		if (mClauseStateIsDirty) {
			return determineClauseState(null) == EprClauseState.Conflict;
		}
		return mEprClauseState == EprClauseState.Conflict;
	}

//	/**
//	 * Returns the literal(s) that were made unfulfillable when this clause became a conflict.
//	 * @return
//	 */
//	public Set<ClauseLiteral> getConflictLiterals() {
//		assert !mClauseStateIsDirty;
//		assert isConflict();
//		assert mConflictLiterals != null : "this should have been set somewhere..";
//		return mConflictLiterals;
//	}
	
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

	public Set<Clause> getGroundings(IDawg<ApplicationTerm, TermVariable> groundingDawg) {
		assert groundingDawg.getColnames().equals(mVariables) : "signatures don't match";

		Set<Clause> result = new HashSet<Clause>();

		for (List<ApplicationTerm> point : groundingDawg){
			TTSubstitution sub = new TTSubstitution(groundingDawg.getColnames(), point);
//			List<Literal> groundLits = new ArrayList<Literal>();
			Set<Literal> groundLits = new HashSet<Literal>();
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


	/**
	 * Checks if in the current decide state a factoring of this conflict clause is possible.
	 * If a factoring is possible, a factored clause is returned.
	 * Otherwise this clause is returned unchanged.
	 * 
	 * @return A factored version of this clause or this clause.
	 */
	public EprClause factorIfPossible() {
		Set<EprPredicate> predsInThisClause = new HashSet<EprPredicate>();
		for (ClauseLiteral cl : mLiterals) {
			if (!(cl instanceof ClauseEprQuantifiedLiteral)) {
				// if the pred only occurs in ground literals we don't need to consider it for factoring
				// (we already did ground factoring at creation)
				continue;
			}
			ClauseEprQuantifiedLiteral ceql = (ClauseEprQuantifiedLiteral) cl;
			predsInThisClause.add(ceql.getEprPredicate());
		}

		for (EprPredicate eprPred : predsInThisClause) {
			// note that ground occurrences may also contribute to a factoring (but one side has to be quantified)
			// so the following set should be just right
			HashSet<ClauseEprLiteral> occurrencesOfSamePredInThisClause = 
					eprPred.getAllEprClauseOccurences().get(this);

			// collect all relevant types of literals
			List<ClauseEprQuantifiedLiteral> positiveQuantifiedOccurencesOfPred = 
					new ArrayList<ClauseEprQuantifiedLiteral>();
			List<ClauseEprGroundLiteral> positiveGroundOccurencesOfPred = 
					new ArrayList<ClauseEprGroundLiteral>();
			List<ClauseEprQuantifiedLiteral> negativeQuantifiedOccurencesOfPred = 
					new ArrayList<ClauseEprQuantifiedLiteral>();
			List<ClauseEprGroundLiteral> negativeGroundOccurencesOfPred = 
					new ArrayList<ClauseEprGroundLiteral>();
			for (ClauseEprLiteral cel : occurrencesOfSamePredInThisClause) {
				if (cel.getPolarity()) {
					if (cel instanceof ClauseEprQuantifiedLiteral) {
						positiveQuantifiedOccurencesOfPred.add((ClauseEprQuantifiedLiteral) cel);
					} else {
						positiveGroundOccurencesOfPred.add((ClauseEprGroundLiteral) cel);
					}
				} else {
					if (cel instanceof ClauseEprQuantifiedLiteral) {
						negativeQuantifiedOccurencesOfPred.add((ClauseEprQuantifiedLiteral) cel);
					} else {
						negativeGroundOccurencesOfPred.add((ClauseEprGroundLiteral) cel);
					}
				}
			}
			
			for (int i = 0; i < positiveQuantifiedOccurencesOfPred.size(); i++) {
				ClauseEprQuantifiedLiteral pqOc = positiveQuantifiedOccurencesOfPred.get(i);
				IDawg<ApplicationTerm, TermVariable> refPointsCurrent = pqOc.getRefutedPoints();
				IDawg<ApplicationTerm, TermVariable> renamedRefPointsCurrent = mDawgFactory.renameColumnsAndRestoreConstants(refPointsCurrent, 
						pqOc.getTranslationForEprPredicate(), pqOc.getArgumentsAsObjects(), pqOc.getEprPredicate().getTermVariablesForArguments());
				for (int j = 0; j < i; j++) {
					ClauseEprQuantifiedLiteral pqOcOther = positiveQuantifiedOccurencesOfPred.get(j);
					assert pqOcOther != pqOc;
					
					IDawg<ApplicationTerm, TermVariable> refPointsOther = pqOcOther.getRefutedPoints();
					IDawg<ApplicationTerm, TermVariable> renamedRefPointsOther = mDawgFactory.renameColumnsAndRestoreConstants(refPointsOther, 
						pqOcOther.getTranslationForEprPredicate(), pqOcOther.getArgumentsAsObjects(), pqOcOther.getEprPredicate().getTermVariablesForArguments());

					
					IDawg<ApplicationTerm, TermVariable> intersection = 
							renamedRefPointsCurrent.intersect(renamedRefPointsOther);
//							pqOc.getRefutedPoints().intersect(pqOcOther.getRefutedPoints());
					
					if (intersection.isEmpty()) {
						continue;
					}
					// we can actually factor
					mEprTheory.getLogger().debug("EPRDEBUG: (EprClause): factoring " + this);
					return mEprTheory.getEprClauseFactory().getFactoredClause(pqOc, pqOcOther);
				}

				for (ClauseEprGroundLiteral pgOc : positiveGroundOccurencesOfPred) {
					if (! pqOc.getRefutedPoints().accepts(
							EprHelpers.convertTermListToConstantList(pgOc.getArguments()))) {
						continue;
					}
					// we can actually factor
					mEprTheory.getLogger().debug("EPRDEBUG: (EprClause): factoring " + this);
					return mEprTheory.getEprClauseFactory().getFactoredClause(pqOc, pgOc);
				}
			}
		}
		// when we can't factor, we just return this clause
		return this;
	}


	public boolean isUnitBelowDecisionPoint(DecideStackDecisionLiteral dsdl) {
		EprClauseState state = determineClauseState(dsdl);
		return state == EprClauseState.Unit;
	}


	public Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> getClauseLitToUnitPointsBelowDecisionPoint(
			DecideStackDecisionLiteral dsdl) {
		Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> res = mDecideStackBorderToClauseLitToUnitPoints.get(dsdl);
		assert res != null;
		return res;
	}
}
