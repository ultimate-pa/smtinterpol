package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprQuantifiedLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.UnitPropagationData;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

public class DecideStackManager {
	

	private final LogProxy mLogger;
	private final EprTheory mEprTheory;
	private final EprStateManager mStateManager;

	private Set<EprClause> mUnitClausesWaitingForPropagation = new HashSet<EprClause>();
	
	private EprDecideStack mDecideStack;

	public DecideStackManager(LogProxy logger, EprTheory eprTheory, EprStateManager eprStateManager) { 
		mLogger = logger;
		mEprTheory = eprTheory;
		mStateManager = eprStateManager;
		mDecideStack = new EprDecideStack();
	}
	
	/**
	 * Takes a set of epr clauses, applies unit propagation until either a conflict is reached, or 
	 * no more propagations are possible.
	 * Some clauses in the input set may have "normal" state, too, we just skip those.
	 * @param unitClauses a set of epr unit clauses
	 * @return null or a conflict epr clause
	 */
	EprClause propagateAll(Set<EprClause> unitClauses) {
		Set<EprClause> conflictsOrUnits = new HashSet<EprClause>(unitClauses);
		while (conflictsOrUnits != null 
				&& !conflictsOrUnits.isEmpty()) {
			EprClause current = conflictsOrUnits.iterator().next(); // just pick any ..

			conflictsOrUnits.remove(current);
			
			if (!current.isUnit()) {
				// current clause has "normal" state --> ignore it
				assert !current.isConflict();
				continue;
			}

			Set<EprClause> propResult = propagateUnitClause(conflictsOrUnits, current);
			
			if (propResult.isEmpty()) {
				continue;
			}
			
			if (propResult.iterator().next().isConflict()) {
				assert propResult.size() == 1;
				return propResult.iterator().next(); 
			}
			conflictsOrUnits.addAll(propResult);
		}
		return null;
	}

	/**
	 * Takes a set of unit clauses, together with one unit clause (not contained in the set)
	 * and makes a propagation according to the unit clause.
	 * If a conflict occurs, a singleton with just the conflict clause is returned.
	 * If additional clauses have been made unit, they are added to the set of unit clauses, and
	 * the updated set is returned.
	 * If no clause has been made conflict or unit by the propagation, the unit clause set is 
	 * returned unchanged.
	 * 
	 * @param conflictsOrUnits
	 * @param unitClause
	 * @return
	 */
	private Set<EprClause> propagateUnitClause(Set<EprClause> conflictsOrUnits, 
			EprClause unitClause) {
		mLogger.debug("EPRDEBUG: EprStateManager.propagateUnitClause(..): " + unitClause);
		assert unitClause.isUnit();
		Set<EprClause> result = new HashSet<EprClause>(conflictsOrUnits);		

		// if we have a unit clause, propagate the literal
		// the set..-method returns the new set of conflicts or units

		// one epr unit clause may yield many propagations 
		// --> iteratively set them, if one produces a conflict, go back to the outer epr dpll loop
		//     if one produces more unit propagations, it is ok to just add them to conflictsOrUnits, because we
		//      it contains unit clauses right now..
		UnitPropagationData upd = unitClause.getUnitPropagationData();
		
		for (DslBuilder dslB : upd.mQuantifiedPropagations) {
			Set<EprClause> newConflictsOrUnits = pushEprDecideStack(dslB);

			if (newConflictsOrUnits != null) {
				if (newConflictsOrUnits.iterator().next().isConflict()) {
					// in case of a conflict further propagations are obsolete
					return newConflictsOrUnits;
				} else if (newConflictsOrUnits.iterator().next().isUnit()) {
					result.addAll(newConflictsOrUnits);
					break; //TODO: surely break here?
				} else {
					assert false : "should not happen";
				}
			}
		}
		
		for (Entry<Literal, Clause> en : upd.mGroundPropagations.entrySet()) {
			Literal propLit = en.getKey();
			mEprTheory.addGroundLiteralToPropagate(propLit, en.getValue());
		}
		return result;
	}
	
	/**
	 * Compute (~choose) a ground conflict clause from the given set of EprConflict clauses
	 *  (which cannot be resolved by taking back an epr decision because there was none needed to
	 *   derive them)
	 * 
	 * We may want to store other groundings somewhere perhaps ??..
	 * 
	 * @param conflicts
	 * @return
	 */
	private Clause chooseGroundingFromConflict(EprClause conflicts) {
		Set<Clause> conflictGroundings = conflicts.getGroundings(conflicts.getConflictPoints());
		//TODO: pick smart?
		return conflictGroundings.iterator().next();
	}

	/**
	 * Resolve the given conflicts, i.e., 
	 *  - backtrack all unit propagations until the last decision 
	 *  - explain the conflict accordingly, possibly learn some clauses
	 *  
	 * @param conflicts
	 * @return A conflict that cannot be resolved in the EprTheory (given the current DPLL decide stack),
	 *    null if there exists none.
	 */
	Clause resolveConflict(EprClause conflict) {
		mLogger.debug("EPRDEBUG: EprStateManager.resolveConflict(..): " + conflict);
		EprClause currentConflict = conflict;
		
		while (true) {
			currentConflict = currentConflict.factorIfPossible();
			assert currentConflict.isConflict();

			currentConflict = backjumpIfPossible(currentConflict);
			assert currentConflict.isConflict();

			if (currentConflict == null) {
				return null;
			}

			DecideStackLiteral topMostDecideStackLiteral = mDecideStack.popDecideStackLiteral();
			if (topMostDecideStackLiteral == null) {
				// we have come to the top of the decide stack --> return the conflict
				Clause groundConflict = chooseGroundingFromConflict(currentConflict);
				return groundConflict;
			}

			if (topMostDecideStackLiteral instanceof DecideStackDecisionLiteral) {
				/*
				 * Reaching here means that the clause 
				 *  - contains two instances of the same predicate with the same polarity 
				 *  which are 
				 *  1 both refuted by the topmost decision
				 *  2 disjoint their allowed groundings
				 *  
				 *  if 1 would not be the case the clause would not be a conflcit anymore
				 *  if 2 would not be the case we would have factored
				 *  
				 *  --> we need to restrict our decision to set one of the two
				 */
				return refine((DecideStackDecisionLiteral) topMostDecideStackLiteral, currentConflict);
			} else if (topMostDecideStackLiteral instanceof DecideStackPropagatedLiteral) {
				assert currentConflict.isConflict();
				currentConflict = 
						explainConflictOrSkip(
								currentConflict, 
								(DecideStackPropagatedLiteral) topMostDecideStackLiteral);
				assert currentConflict.isConflict(); // need to call a determineState here??
			} else {
				assert false : "should not happen";
			}
		}
	}
	
	/**
	 * The top of the decision stack is a decision and we have a conflict clause.
	 * Refine that decision such that the conflict clause becomes a unit clause.
	 * @param topMostDecideStackLiteral 
	 * @param currentConflict
	 * @return a ground conflict if the new decision immediately led to one
	 */
	private Clause refine(DecideStackDecisionLiteral topMostDecideStackLiteral, EprClause currentConflict) {
	
		// find all clause literals with the same predicate and polarity
		Set<ClauseEprLiteral> literalsMatchingDecision = new HashSet<ClauseEprLiteral>();
		for (ClauseLiteral cl : currentConflict.getLiterals()) {
			if (cl instanceof ClauseEprLiteral) {
				ClauseEprLiteral cel = (ClauseEprLiteral) cl;
				if (cel.getPolarity() != topMostDecideStackLiteral.getPolarity()) {
					continue;
				}
				if (cel.getEprPredicate() != topMostDecideStackLiteral.getEprPredicate()) {
					continue;
				}
				literalsMatchingDecision.add(cel);
			}
		}
		// (invariant here: the dawgs of all cl literalsMatchingDecision - the refuted points, 
		//  as all points are refuted on those dawgs - are all disjoint)

		// pick one literal (TODO: this is a place for a heuristic strategy)
		ClauseEprLiteral pickedLit = literalsMatchingDecision.iterator().next();
		//.. and remove its dawg from the decision
		IDawg<ApplicationTerm, TermVariable> newDawg = mEprTheory.getDawgFactory().copyDawg(topMostDecideStackLiteral.getDawg());
		for (IEprLiteral dsl : pickedLit.getPartiallyConflictingDecideStackLiterals()) {
			assert EprHelpers.haveSameSignature(dsl.getDawg(), newDawg);
			newDawg.removeAll(dsl.getDawg());
		}

		// revert the decision
		DecideStackLiteral dsdl = mDecideStack.popDecideStackLiteral();
		assert dsdl == topMostDecideStackLiteral;
	
		// make the new decision with the new dawg
		DslBuilder dslb = new DslBuilder(dsdl.getPolarity(), dsdl.getEprPredicate(), newDawg, true);
		Set<EprClause> newConflictsOrUnits = pushEprDecideStack(dslb);
		assert currentConflict.isUnit();
		return resolveConflictOrStoreUnits(newConflictsOrUnits);
	}

	/**
	 * Checks if the given conflict clause allows backjumping below an epr decision.
	 * If the argument clause does allow backjumping (i.e. is unit below the last epr decision), we
	 *  backtrack the decision an propagate according to the unit clause that the argument has become.
	 *  These propagations may result in another conflict, which we then return, or they may just at saturation,
	 *   then we return null.
	 * If the argument does not allow backjumping we return it unchanged.
	 * @param currentConflict a conflict clause
	 * @return a) the input conflict if backjumping is impossible, 
	 *         b) another conflict if backjumping and propagation led to it, 
	 *         c) null if backjumping was done and did not lead to a conflict through unit propagation
	 */
	private EprClause backjumpIfPossible(EprClause currentConflict) {
		if (!mDecideStack.containsDecisions()) {
			return currentConflict;
		}
		
		DecideStackDecisionLiteral lastDecision = mDecideStack.getLastDecision();
		
		if (currentConflict.isUnitBelowDecisionPoint(lastDecision)) {
			// we can backjump
			popEprDecideStackUntilAndIncluding(lastDecision);
			
			assert currentConflict.isUnit();
			// after the changes to the decide stack, is a unit clause --> just propagate accordingly
			mUnitClausesWaitingForPropagation.add(currentConflict);
			mLogger.debug("EPRDEBUG: (EprStateManager): backjumping, new unit clause/former conflict: " 
					+ currentConflict + " reverted decision: " + lastDecision);
			return null;
		}
		return currentConflict;
	}

	/**
	 * Explains a conflict given a decide stack literal
	 *  - if the decide stack literal did not contribute to the conflict (does not contradict one 
	 *   of the literals in the conflict), return the conflict unchanged (DPLL operation "skip")
	 *  - otherwise, if the decide stack literal contributed to the conflict, return the resolvent
	 *    of the conflict and the unit clause responsible for setting the decide stack literal 
	 *     (DPLL operation "explain")
	 * @param conflict
	 * @param propagatedLiteral
	 * @return the resolvent from the conflict and the reason for the unit propagation of decideStackLiteral
	 */
	private EprClause explainConflictOrSkip(EprClause conflict, DecideStackPropagatedLiteral propagatedLiteral) {
		
		//look for the ClauseLiteral that propagatedLiteral conflicts with
		Set<ClauseEprQuantifiedLiteral> relevantConfLits = new HashSet<ClauseEprQuantifiedLiteral>();
		for (ClauseLiteral cl : conflict.getLiterals()) {
			if (cl instanceof ClauseEprQuantifiedLiteral) {
				ClauseEprQuantifiedLiteral ceql = (ClauseEprQuantifiedLiteral) cl;
				if (ceql.getPartiallyConflictingDecideStackLiterals().contains(propagatedLiteral)) {
					relevantConfLits.add(ceql);
				}
			}
		}
		
		if (relevantConfLits.size() > 1) {
			assert false : "TODO: understand this -- factoring? what if factoring is not applicable??";
			return null;
		} else if (relevantConfLits.size() == 1) {
			// normal explain case --> return the resolvent
			ClauseEprQuantifiedLiteral confLit = relevantConfLits.iterator().next();
			return mEprTheory.getEprClauseFactory().createResolvent(confLit, propagatedLiteral.getReasonClauseLit());
		} else {
			//propagatedLiteral has nothing to do with conflictClause --> skip
			return conflict;
		}
	}

	/**
	 *
	 * @return 	A DecideStackLiteral for an EprPredicate with incomplete model 
	 *           or null if all EprPredicates have a complete model.
	 **/
	DslBuilder getNextDecision() {
		for (EprPredicate ep : mEprTheory.getStateManager().getAllEprPredicates()) {
			DslBuilder decision = ep.getNextDecision();
			if (decision != null) {
				return decision;
			}
		}
		return null;
	}
	
	/**
	 * 
	 * plan:
	 * - remove the conflicting point (option: more points?)
	 * - remove the top of the decide stack until the conflicting literal
	 * - if the conflictingDsl was a decision, resetting that decision is enough.. (just go back to DPLLEngine)
	 * - if the conflictingDsl was propagated, resolve its unit clause (it became a conflict through the setLiteral)
	 * 
	 * @param egpl the epr ground literal that the DPLLEngine has set and which contradicts the current epr decide stack
	 * @param conflictingDsl the decide stack literal that egpl has the conflict with
	 * @return an unresolvable groundConflict if there is one, null if there is none 
	 *         (i.e. changing an epr decision removed the inconsistency)
	 */
	Clause resolveDecideStackInconsistency(EprGroundPredicateLiteral egpl, DecideStackLiteral conflictingDsl) {
		
		// pop the decide stack above conflictingDsl
		boolean success = popEprDecideStackUntilAndIncluding(conflictingDsl);	
		assert success;
		
		
		if (conflictingDsl instanceof DecideStackDecisionLiteral) {
			// the old decision has been reverted, make a new one that is consistent
			// with the setting of egpl
			
			// TODO: this is a place for a strategy
			// right now: make decision as before, except for that one point
			IDawg<ApplicationTerm, TermVariable> newDawg = 
					mEprTheory.getDawgFactory().copyDawg(conflictingDsl.getDawg());
			newDawg.removeAll(egpl.getDawg()); // (should be one point only)
			
			DslBuilder newDecision = 
					new DslBuilder(
							conflictingDsl.getPolarity(), conflictingDsl.getEprPredicate(), newDawg, true);
			
			Set<EprClause> conflictsOrUnits = pushEprDecideStack(newDecision);
			return resolveConflictOrStoreUnits(conflictsOrUnits);
		} else if (conflictingDsl instanceof DecideStackPropagatedLiteral) {
			// the propagated literal that was the root of the inconsistency has been popped
			// its reason for propagation should be a conflict now instead of a unit
			// resolve that conflict
			EprClause propReason = ((DecideStackPropagatedLiteral) conflictingDsl).getReasonClauseLit().getClause();
			propReason.updateStateWrtDecideStackLiteral(
					egpl, 
					egpl.getEprPredicate().getAllEprClauseOccurences().get(propReason));
			assert propReason.isConflict();
			return resolveConflict(propReason);
		} else {
			assert false : "should not happen";
		}
		return null;
	}

	
	/**
	 * Pop the decide stack until -and including the argument- dsl is reached.
	 * 
	 * @param dsl
	 * @return true if dsl was on the decide stack false otherwise
	 */
	private boolean popEprDecideStackUntilAndIncluding(DecideStackLiteral dsl) {
		assert dsl != null;
		while (true) {
			DecideStackLiteral currentDsl = mDecideStack.popDecideStackLiteral();
			if (currentDsl == dsl) {
				return true;
			} else if (currentDsl == null) {
				assert false : 
					"could not find the conflicting decide stack literal that was found earlier";
				return false;
			}
		}
	}
	
	/**
	 * Given an epr ground literal look if there is a decide stack literal that contradicts it.
	 * (this is called when the DPLLEngine sets an epr literal an we need to know if the two decide stacks
	 *  of dpll engine and epr theory are still consistent wrt each other)
	 * Note that the result should be unique here, because on the epr decide stack we don't set points twice
	 *  (or do we?..)
	 * @param egpl
	 * @return the decide stack literal that contradicts egpl if there exists one, null otherwise
	 */
	DecideStackLiteral searchConflictingDecideStackLiteral(EprGroundPredicateLiteral egpl) {
		// TODO not fully sure if each point is set only once on the epr decide stack
		//  --> if not, we probably want to 
		for (IEprLiteral dsl : egpl.getEprPredicate().getEprLiterals()) { 
			if (!(dsl instanceof DecideStackLiteral)) {
				continue;
			}
			if (dsl.getPolarity() != egpl.getPolarity()
					&& ! egpl.getDawg().intersect(dsl.getDawg()).isEmpty()) {
				return (DecideStackLiteral) dsl;
			}
		}
		return null;
	}
	
	public Clause resolveConflictOrStoreUnits(Set<EprClause> conflictOrUnits) {
		if (conflictOrUnits == null || conflictOrUnits.isEmpty()) {
			return null;
		}
		if (conflictOrUnits.iterator().next().isConflict()) {
			return resolveConflict(conflictOrUnits.iterator().next());
		}
		if (conflictOrUnits.iterator().next().isUnit()) {
			mUnitClausesWaitingForPropagation.addAll(conflictOrUnits);
		}
		return null;
	}
	
	/**
	 * Apply the consequences of setting the given epr decide stack literal
	 *  - wrt. the decide stack of the DPLLEngine
	 *  - wrt. the epr clauses
	 *  both can yield conflicts or unit propagations.
	 * 
	 * @param dsl
	 * @return 
	 */
	Set<EprClause> pushEprDecideStack(DslBuilder dslb) {
		dslb.setDecideStackIndex(mDecideStack.size());
		DecideStackLiteral dsl = dslb.build();
		
		// setting the decideStackLiteral means that we have to set all ground atoms covered by it
		// in the DPLLEngine
		// however, if we propagate a ground literal here, we also have to give a ground unit clause for it
		// creating this ground unit clause may lead to new ground atoms, thus we make a copy to a void
		// concurrent modification of the list of DPLLAtoms, and repeat until the copy doss not change
		// TODO: can we do this nicer?
		boolean newDPLLAtoms = true;
		while (newDPLLAtoms) {
			HashSet<EprGroundPredicateAtom> copy = new HashSet<EprGroundPredicateAtom>(dsl.getEprPredicate().getDPLLAtoms());
			for (EprGroundPredicateAtom atom : copy) {
				EprClause conflict = mStateManager.setGroundAtomIfCoveredByDecideStackLiteral(dsl, atom);
				if (conflict != null) {
					return new HashSet<EprClause>(Collections.singleton(conflict));
				}
			}
			newDPLLAtoms = !copy.equals(dsl.getEprPredicate().getDPLLAtoms());
		}
		
		// inform the clauses...
		// check if there is a conflict
		Set<EprClause> conflictsOrPropagations = 
				mStateManager.getEprClauseManager().updateClausesOnSetEprLiteral(dsl);

		mDecideStack.pushDecideStackLiteral(dsl);
		
	    return conflictsOrPropagations;
	}

	/**
	 * Returns true iff the EprTheory has currently made no own decisions.
	 * Thus when we derived something in the epr theory, we can propagate it, otherwise
	 * we can only suggest it..
	 * @return
	 */
	 boolean isDecisionLevel0() {
		return !mDecideStack.containsDecisions();
	 }
	 
	 void pushOnSetLiteral(Literal l) {
		 mDecideStack.pushSetLiteral(l);
	 }
	 
	 void popOnBacktrackLiteral(Literal l) {
		 mDecideStack.popBacktrackLiteral(l);
	 }


	Clause doPropagations() {
		HashSet<EprClause> toProp = new HashSet<EprClause>(mUnitClausesWaitingForPropagation);
		mUnitClausesWaitingForPropagation = new HashSet<EprClause>();
		EprClause conflict = propagateAll(toProp);
		if (conflict == null) {
			return null;
		} else {
			assert conflict.isConflict();
			Clause groundConflict =  resolveConflict(conflict);
			return groundConflict;
		}
	}

	public void push() {
		mDecideStack.push();
	}

	public void pop() {
		mUnitClausesWaitingForPropagation.clear();
		mDecideStack.pop();
	}
	
	public void removeFromUnitClauseSet(EprClause eprClause) {
		mUnitClausesWaitingForPropagation.remove(eprClause);
	}

	private static class EprDecideStack {
		private final List<DecideStackEntry> mStack = new LinkedList<DecideStackEntry>();
		
		private int lastNonPushMarkerIndex = -1;
		private int lastPushMarkerIndex = -1;
		
		private DecideStackLiteral lastNonPushMarker;
		private DecideStackPushMarker lastPushMarker;
		private DecideStackEntry lastElement;
		private DecideStackDecisionLiteral lastDecision;
		
		private Map<Literal, DecideStackLiteralMarker> mLiteralToMarker = 
				new HashMap<Literal, DecideStackLiteralMarker>();
		
		/**
		 * Places a marker for a setLiteral operation in the EprTheory.
		 */
		void pushSetLiteral(Literal l) {
			DecideStackLiteralMarker marker = new DecideStackLiteralMarker(l, mStack.size());
			mStack.add(marker);
			assert !mLiteralToMarker.containsKey(l);
			mLiteralToMarker.put(l, marker);
		}

		public DecideStackDecisionLiteral getLastDecision() {
			assert lastDecision != null;
			return lastDecision;
		}

		/**
		 * @return true iff the decide stack contains one or more DecideStackDecisionLiterals
		 */
		public boolean containsDecisions() {
			return lastDecision != null;
		}

		void popBacktrackLiteral(Literal l) {
			DecideStackLiteralMarker marker = mLiteralToMarker.remove(l);
			if (marker.mIndex >= mStack.size()) {
				// removed the marker through a pop() before, nothing to do
				return;
			}
			List<DecideStackEntry> suffix = mStack.subList(marker.mIndex, mStack.size());
			for (DecideStackEntry dse : suffix) {
				if (dse instanceof DecideStackLiteral) {
					((DecideStackLiteral) dse).unregister();
				}
			}
			suffix.clear();
			updateInternalFields();
		}
		
		DecideStackLiteral popDecideStackLiteral() {
			if (lastNonPushMarker == null) {
				return null;
			}

			DecideStackLiteral result = lastNonPushMarker;
			mStack.remove(result);
			result.unregister();

			updateInternalFields();

			return result;
		}
		
		void pushDecideStackLiteral(DecideStackLiteral dsl) {
			mStack.add(dsl);
			lastNonPushMarker = dsl;
			lastNonPushMarkerIndex = mStack.size() - 1;
			if (dsl instanceof DecideStackDecisionLiteral) {
				lastDecision = (DecideStackDecisionLiteral) dsl;
			}
		}
		
		/**
		 * Returns the decide stack entries above the last push marker.
		 */
		List<DecideStackEntry> peek() {
			List<DecideStackEntry> suffix = mStack.subList(lastPushMarkerIndex + 1, mStack.size());
			return suffix;
		}

		void pop() {
			assert lastPushMarker != null : "already popped all push markers";
			

			List<DecideStackEntry> suffix = mStack.subList(lastPushMarkerIndex, mStack.size());
			for (DecideStackEntry dse : suffix) {
				if (dse instanceof DecideStackLiteral) {
					((DecideStackLiteral) dse).unregister();
				}
			}
			suffix.clear();
			
			
			updateInternalFields();
		}
		
		void push() {
			DecideStackPushMarker pm = new DecideStackPushMarker();
			lastPushMarker = pm;
			lastPushMarkerIndex = mStack.size();
			mStack.add(pm);
		}

		private void updateInternalFields() {
			// change the fields accordingly -- search for the next non push marker
			ListIterator<DecideStackEntry> it = mStack.listIterator(mStack.size());

			boolean foundNonPushMarker = false;
			boolean foundPushMarker = false;
			boolean foundLastDecision = lastDecision == null || lastDecision.mIndex < mStack.size();

			while (it.hasPrevious()) {
				DecideStackEntry prev = it.previous();
				
				if (!foundPushMarker && prev instanceof DecideStackPushMarker) {
					lastPushMarker = (DecideStackPushMarker) prev;
					lastPushMarkerIndex = it.previousIndex() + 1;
					foundPushMarker = true;
				}
				
				if (!foundNonPushMarker && prev instanceof DecideStackLiteral) {
					lastNonPushMarker = (DecideStackLiteral) prev;
					lastNonPushMarkerIndex = it.previousIndex() + 1;
					foundNonPushMarker = true;
				}
				
				if (!foundLastDecision && prev instanceof DecideStackDecisionLiteral) {
					lastDecision = (DecideStackDecisionLiteral) prev;
					foundLastDecision = true;
				}

				if (foundPushMarker && foundNonPushMarker && foundLastDecision) {
					break;
				}
			}
			if (!foundPushMarker) {
				lastPushMarker = null;
				lastPushMarkerIndex = -1;
			}
			if (!foundNonPushMarker) {
				lastNonPushMarker = null;
				lastNonPushMarkerIndex = -1;
			}
			if (!foundLastDecision) {
				lastDecision = null;
			}
		}
		
		public int size() {
			return mStack.size();
		}
		
		@Override
		public String toString() {
			return mStack.toString();
		}
	}
}
