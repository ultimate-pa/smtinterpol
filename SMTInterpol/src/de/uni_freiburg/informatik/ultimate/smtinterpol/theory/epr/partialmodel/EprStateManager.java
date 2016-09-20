package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EqualityManager;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprGroundLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprQuantifiedLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClauseFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClauseState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

/**
 * This class is responsible for managing everything that is connected to the
 * current decide state of the EprTheory.
 * This entails:
 *  - managing the Epr decide stack according to push/pop and setLiteral commands
 *   as well as internal propagations and decisions
 *  - telling clauses to update their states (or so..)
 * 
 * @author Alexander Nutz
 */
public class EprStateManager {

	private Stack<EprPushState> mPushStateStack = new Stack<EprPushState>();
	
	private ScopedHashSet<ApplicationTerm> mUsedConstants = new ScopedHashSet<ApplicationTerm>();

	public EqualityManager mEqualityManager;
	private EprTheory mEprTheory;
	private Theory mTheory;
	private CClosure mCClosure;
	private LogProxy mLogger;
	
	ScopedHashSet<EprPredicate> mAllEprPredicates = new ScopedHashSet<EprPredicate>();
	
	/**
	 * Remembers for each DPLLAtom in which EprClauses it occurs (if any).
	 */
	HashMap<DPLLAtom, HashSet<EprClause>> mDPLLAtomToClauses = 
			new HashMap<DPLLAtom, HashSet<EprClause>>();

	private EprClauseFactory mEprClauseFactory;

	private DawgFactory<ApplicationTerm, TermVariable> mDawgFactory;

	private Set<EprClause> mUnitClausesWaitingForPropagation = new HashSet<EprClause>();

	private HashMap<Literal, EprGroundPredicateLiteral> mLiteralToEprGroundPredicateLiteral = 
			new HashMap<Literal, EprGroundPredicateLiteral>();


	private Stack<DecideStackDecisionLiteral> mDecisions = new Stack<DecideStackDecisionLiteral>();
	
	public EprStateManager(EprTheory eprTheory) {
		mPushStateStack.add(new EprPushState(0));

		mEprTheory = eprTheory;
		mEqualityManager =  eprTheory.getEqualityManager();
		mTheory = eprTheory.getTheory();
		mCClosure = eprTheory.getCClosure();
		mEprClauseFactory = eprTheory.getEprClauseFactory();
		mLogger = eprTheory.getLogger();
	}
	
	/**
	 * Executes a basic DPLL loop starting with the current decide state.
	 * every iteration of the topmost loop  roughly triggers one rule in the rule-based
	 * notation of DPLL.
	 * 
	 * If this method finds a conflict that goes back to a DPLL (ground) decision that conflict
	 * is returned.
	 * If this method terminates without returning a conflict (thus returning null), then the current
	 * Epr decide state must constitute a complete model for all EprPredicates.
	 * 
	 * @return a ground conflict if one is found, null otherwise.
	 */
	public Clause eprDpllLoop() {

		while (true) {

			DslBuilder nextDecision = getNextDecision();
			if (nextDecision == null) {
				// model is complete
				return null;
			}

			// make the decision
			if (!nextDecision.isOnePoint()) {
				Set<EprClause> conflictsOrUnits = pushEprDecideStack(nextDecision);
				return resolveConflictOrStoreUnits(conflictsOrUnits);
			} else {
				// if the next requested decision is ground, suggest it to the DPLLEngine, and give 
				// back control to the DPLLEngine
				DecideStackLiteral dsl = nextDecision.build();
				Literal groundDecision = dsl.getEprPredicate()
						.getAtomForTermTuple(
								new TermTuple(dsl.getPoint().toArray(
										new ApplicationTerm[dsl.getPoint().size()])), // TODO: make nicer
								mTheory, 0); //TODO assertionstacklevel
				assert groundDecision.getAtom().getDecideStatus() == null : "If this is not the case, then"
						+ "it might be dangerous to return null: if null is returned to computeConflictClause,"
						+ "this means the EprTheory says there is no conflict and I have a full model..";
				mEprTheory.addGroundDecisionSuggestion(groundDecision);
				return null;
			}
		}
	}


	/**
	 * Takes a set of epr clauses, applies unit propagation until either a conflict is reached, or 
	 * no more propagations are possible.
	 * Some clauses in the input set may have "normal" state, too, we just skip those.
	 * @param unitClauses a set of epr unit clauses
	 * @return null or a conflict epr clause
	 */
	private EprClause propagateAll(Set<EprClause> unitClauses) {
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
		// TODO: should work like this (one unit prop for every iteration),
		//   but is there an unnecessary computation involved when determining the clause states again?


		// one epr unit clause may yield many propagations 
		// --> iteratively set them, if one produces a conflict, go back to the outer epr dpll loop
		//     if one produces more unit propagations, it is ok to just add them to conflictsOrUnits, because we
		//      it contains unit clauses right now..
		Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> clToUps = 
				unitClause.getClauseLitToUnitPoints();
		
		for (Entry<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> en : clToUps.entrySet()) {
			ClauseLiteral cl = en.getKey();
			
			if (cl instanceof ClauseEprQuantifiedLiteral) {
				ClauseEprQuantifiedLiteral ceql = (ClauseEprQuantifiedLiteral) cl;
				
				IDawg<ApplicationTerm, TermVariable> dawg = en.getValue();
//				DecideStackPropagatedLiteral prop = new DecideStackPropagatedLiteral(
				DslBuilder propB = new DslBuilder(
						ceql.getPolarity(), 
						ceql.getEprPredicate(),
						mDawgFactory.renameColumnsAndRestoreConstants(
								dawg, 
								ceql.getTranslationForEprPredicate(), 
								ceql.getArgumentsAsObjects(),
								ceql.getEprPredicate().getTermVariablesForArguments()),
						ceql,
						false);

				Set<EprClause> newConflictsOrUnits = pushEprDecideStack(propB);

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
			} else {
				// the unit literal is ground --> store it for propagation to dpll engine, no further effects for epr
				assert clToUps.entrySet().size() == 1;
				Entry<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> item = clToUps.entrySet().iterator().next(); //TODO: not nice
				Literal propLit = item.getKey().getLiteral();
				mEprTheory.addGroundLiteralToPropagate(propLit, cl.getUnitGrounding(propLit));
			}
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
	private Clause resolveConflict(EprClause conflict) {
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

			DecideStackLiteral topMostDecideStackLiteral = popEprDecideStack();
			if (topMostDecideStackLiteral == null) {
				// we have come to the top of the decide stack --> return the conflict
				return chooseGroundingFromConflict(currentConflict);
			}

//			// backtrack the literal
//			popEprDecideStack();

			if (topMostDecideStackLiteral instanceof DecideStackDecisionLiteral) {
				assert mDecisions.peek() == topMostDecideStackLiteral : "something wrong with decisions stack";
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
				learnClause(currentConflict);
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
		IDawg<ApplicationTerm, TermVariable> newDawg = mDawgFactory.copyDawg(topMostDecideStackLiteral.getDawg());
		for (IEprLiteral dsl : pickedLit.getPartiallyConflictingDecideStackLiterals()) {
			assert EprHelpers.haveSameSignature(dsl.getDawg(), newDawg);
			newDawg.removeAll(dsl.getDawg());
		}

		// revert the decision
		DecideStackLiteral dsdl = popEprDecideStack();
		assert dsdl == topMostDecideStackLiteral;
	
		// make the new decision with the new dawg
		DslBuilder dslb = new DslBuilder(dsdl.getPolarity(), dsdl.getEprPredicate(), newDawg, true);
		Set<EprClause> newConflictsOrUnits = pushEprDecideStack(dslb);
		assert currentConflict.isUnit();
		return resolveConflictOrStoreUnits(newConflictsOrUnits);
	}

	public void learnClause(EprClause currentConflict) {
		// TODO: as is this method seems weird, architecture-wise
		// the registration has to be done for any epr clause that we add to our formula
		// --> just ditch this method, use register.. instead??
		registerEprClause(currentConflict);
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
		if (mDecisions.isEmpty()) {
			return currentConflict;
		}
		
		DecideStackDecisionLiteral lastDecision = mDecisions.peek();
		
		if (currentConflict.isUnitBelowDecisionPoint(lastDecision)) {
			// we can backjump
			popEprDecideStackUntilAndIncluding(lastDecision);
			
			assert currentConflict.isUnit();
			// after the changes to the decide stack, is a unit clause --> just propagate accordingly
			mUnitClausesWaitingForPropagation.add(currentConflict);
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
	private DslBuilder getNextDecision() {
		for (EprPredicate ep : getAllEprPredicates()) {
			DslBuilder decision = ep.getNextDecision();
			if (decision != null) {
				return decision;
			}
		}
		return null;
	}

	public void push() {
		mPushStateStack.push(new EprPushState(mPushStateStack.size()));
		mAllEprPredicates.beginScope();
		mUsedConstants.beginScope();
		mEprClauseFactory.push();
	}
	
	public void pop() {
		EprPushState poppedState = mPushStateStack.pop();
		for (EprClause c : poppedState.getClauses()) {
			c.disposeOfClause();
		}
		mAllEprPredicates.endScope();
		mUsedConstants.endScope();
		mEprClauseFactory.pop();
	}

	////////////////// 
	////////////////// methods that change the epr solver state (state of clauses and/or decide stack)
	////////////////// 

	/**
	 * Update the state of the epr solver according to a ground epr literal being set.
	 * This entails
	 *  - updating the decide stack --> EDIT: .. not, the ground decide stack is managed by the DPLLEngine
	 *  - triggering updates of clause states for the right clauses (maybe somewhere else..)
	 * @param literal
	 * @return
	 */
	public Clause setEprGroundLiteral(Literal literal) {
		//TODO: what do we have to do in the case of an _epr_ ground literal in contrast
		//  to a normal ground literal???
		//  --> the main difference is that it may interact with the epr decide stack
		//      thus we have to check for contradictions before calling update... (which assumes consistency of the "set points" for each clauseliteral)
		//   after that we treat it like a decide stack literal (again because of the interactions with other literals over epr predicates)
		
		EprGroundPredicateLiteral egpl = new EprGroundPredicateLiteral(literal, mDawgFactory, this);
		
		DecideStackLiteral conflictingDsl = searchConflictingDecideStackLiteral(egpl);
		
		if (conflictingDsl != null) {
			Clause unresolvableGroundConflict = resolveDecideStackInconsistency(egpl, conflictingDsl);
			if (unresolvableGroundConflict != null) {
				// setting literal resulted in a conflict that cannot be resolved by reverting epr decisions
				return unresolvableGroundConflict;
			}
		}

		Set<EprClause> confOrUnits = updateClausesOnSetEprLiteral(egpl);
		return resolveConflictOrStoreUnits(confOrUnits);
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
	private Clause resolveDecideStackInconsistency(EprGroundPredicateLiteral egpl, DecideStackLiteral conflictingDsl) {
		
		// pop the decide stack above conflictingDsl
		boolean success = popEprDecideStackUntilAndIncluding(conflictingDsl);	
		assert success;
		
		
		if (conflictingDsl instanceof DecideStackDecisionLiteral) {
			// the old decision has been reverted, make a new one that is consistent
			// with the setting of egpl
			
			// TODO: this is a place for a strategy
			// right now: make decision as before, except for that one point
			IDawg<ApplicationTerm, TermVariable> newDawg = 
					mDawgFactory.copyDawg(conflictingDsl.getDawg());
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
			DecideStackLiteral currentDsl = popEprDecideStack();
			if (currentDsl == dsl) {
				return true;
			} else if (currentDsl == null) {
				assert false : 
					"could not find the conflicting decide stack literal that was found earlier";
				return false;
			}
		}
	}
	
	private DecideStackLiteral popEprDecideStack() {
		
		ListIterator<EprPushState> pssIt = mPushStateStack.listIterator(mPushStateStack.size());
		
		while (pssIt.hasPrevious()) {
			EprPushState currentPushState = pssIt.previous();
			
			DecideStackLiteral dsl = currentPushState.popDecideStack();
			
			assert dsl == null || 
					dsl.getIndex().indexOfPushState == currentPushState.getIndex() 
					: "check dsl indices!";

			if (dsl instanceof DecideStackDecisionLiteral) {
				DecideStackDecisionLiteral dec = mDecisions.pop();
				assert dec == dsl;
			}

			if (dsl != null) {
				updateClausesOnBacktrackDecideStackLiteral(dsl);
				return dsl;
			}
		}	
		return null;
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
	private DecideStackLiteral searchConflictingDecideStackLiteral(EprGroundPredicateLiteral egpl) {
		// TODO not fully sure if each point is set only once on the epr decide stack
		//  --> if not, we probably want to 
		for (DecideStackLiteral dsl : egpl.getEprPredicate().getDecideStackLiterals()) { 
			if (dsl.getPolarity() != egpl.getPolarity()
					&& ! egpl.getDawg().intersect(dsl.getDawg()).isEmpty()) {
				return dsl;
			}
		}
		return null;
	}
	
	public void unsetEprGroundLiteral(Literal literal) {
		EprGroundPredicateLiteral egpl = mLiteralToEprGroundPredicateLiteral.get(literal);
		assert egpl != null;
		egpl.unregister();
		updateClausesOnBacktrackDpllLiteral(literal);
	}
	
	public Clause setDpllLiteral(Literal literal) {
		Set<EprClause> conflictOrUnits = updateClausesOnSetDpllLiteral(literal);
		return resolveConflictOrStoreUnits(conflictOrUnits);
	}

	private Clause resolveConflictOrStoreUnits(Set<EprClause> conflictOrUnits) {
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
	
	public void unsetDpllLiteral(Literal literal) {
		updateClausesOnBacktrackDpllLiteral(literal);
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
	private Set<EprClause> pushEprDecideStack(DslBuilder dslb) {
		
		dslb.setIndexOnPushStateStack(mPushStateStack.peek().getDecideStackHeight());
		dslb.setPushStateStackIndex(mPushStateStack.size() - 1);
		DecideStackLiteral dsl = dslb.build();
		
		if (dsl instanceof DecideStackDecisionLiteral) {
			mDecisions.push((DecideStackDecisionLiteral) dsl);
		}
		
		// setting the decideStackLiteral means that we have to set all ground atoms covered by it
		// in the DPLLEngine
		for (EprGroundPredicateAtom atom : dsl.getEprPredicate().getDPLLAtoms()) {
			EprClause conflict = setGroundAtomIfCoveredByDecideStackLiteral(dsl, atom);
			if (conflict != null) {
				return new HashSet<EprClause>(Collections.singleton(conflict));
			}
		}
		
		// inform the clauses...
		// check if there is a conflict
		Set<EprClause> conflictsOrPropagations = 
				updateClausesOnSetEprLiteral(dsl);

		mPushStateStack.peek().pushDecideStackLiteral(dsl);
		
	    return conflictsOrPropagations;
	}

	/**
	 * When we have an epr decide stack literal, and an atom who both talk about the same epr predicate,
	 * we
	 *  - check if the dawg of the dsl contains the atom's point, if not, we do nothing
	 *  - otherwise we have to tell the dpll engine about it in form of a propagation (sideeffect) (or possibly a suggestion)
	 *  - if the atom is already set in the dpll engine the other way, then we return a conflict
	 * @param dsl
	 * @param atom
	 * @return
	 */
	public EprClause setGroundAtomIfCoveredByDecideStackLiteral(DecideStackLiteral dsl,
			EprGroundPredicateAtom atom) {
		if (! dsl.getDawg().accepts(
				EprHelpers.convertTermArrayToConstantList(atom.getArguments()))) {
			return null;
		}
		
		if (atom.getDecideStatus() == null) {
			// the atom is undecided in the DPLLEngine
			// --> propagate it
			// TODO: we will have to keep the reason for the propagation in store, the DPLLEngine will ask..
			
			Literal groundLiteral = dsl.getPolarity() ?
								atom :
									atom.negate();
			if (dsl instanceof DecideStackPropagatedLiteral) {
				mEprTheory.addGroundLiteralToPropagate(
						groundLiteral, 
						((DecideStackPropagatedLiteral) dsl).getReasonClauseLit().getUnitGrounding(groundLiteral));
			} else {
				// we have a decision decide stack literal 
				// --> suggest to the DPLLEngine to set it the same way
				// TODO: not so clear if this is used at all..
//				assert false : "TODO: think this over";
//				mEprTheory.addGroundDecisionSuggestion(groundLiteral);
			}

		} else 	if (atom.getDecideStatus() == null 
				|| dsl.mPolarity == (atom.getDecideStatus() == atom)) {
			// the atom is decided the other way in the DPLLEngine
			//  --> there is a conflict.. return the conflict clause which is the unit clause responsible for
			//     propagating the decide stack literal
			assert dsl instanceof DecideStackPropagatedLiteral :
				"we have made a decision that contradicts the state of an eprGroundLiteral in the DPLLEngine"
				+ " directly. this should not happen.";
			return ((DecideStackPropagatedLiteral) dsl)
				.getReasonClauseLit().getClause();
		}
		return null;
	}

	/**
	 * Ask the clauses what happens if dcideStackQuantifiedLiteral is set.
	 * Returns a conflict that the setting of the literal would induce, null if there is none.
	 * 
	 * @param literalToBeSet
	 * @return an EprClause that is Unit or Conflict if there is one, null otherwise
	 */
	private Set<EprClause> updateClausesOnSetEprLiteral(IEprLiteral literalToBeSet) {
		
		HashMap<EprClause, HashSet<ClauseEprLiteral>> allOccurences = 
				literalToBeSet.getEprPredicate().getAllEprClauseOccurences();
		
		Set<EprClause> unitClauses = new HashSet<EprClause>();
	
		for (Entry<EprClause, HashSet<ClauseEprLiteral>> en : allOccurences.entrySet()) {
			EprClause eprClause = en.getKey();
			
			eprClause.updateStateWrtDecideStackLiteral(literalToBeSet, en.getValue());

			if (eprClause.isConflict()) {
				return new HashSet<EprClause>(Collections.singleton(eprClause));
			} else if (eprClause.isUnit()) {
				unitClauses.add(eprClause);
			}
		}
		
		if (! unitClauses.isEmpty()) {
			return unitClauses;
		}

		return null;
	}

	/**
	 * this -might- be unnecessary
	 *   -- depending on whether the clauses look at the decide stack themselves anyway..
	 *     --> still unclear.. (TODO)
	 * @param dsl
	 */
	private void updateClausesOnBacktrackDecideStackLiteral(DecideStackLiteral dsl) {
		HashMap<EprClause, HashSet<ClauseEprLiteral>> allOccurences = 
				dsl.getEprPredicate().getAllEprClauseOccurences();
		
		for (Entry<EprClause, HashSet<ClauseEprLiteral>> en : allOccurences.entrySet()) {
			EprClause eprClause = en.getKey();
			
			eprClause.backtrackStateWrtDecideStackLiteral(dsl);

//			if (eprClause.isConflict()) {
//				assert false : "?";
//			} else if (eprClause.isUnit()) {
//				assert false : "?";
//			}
		}
	}

	/**
	 * Inform all the EprClauses that contain the atom (not only the
	 * literal!) that they have to update their fulfillment state.
	 * 
	 * Note: This is not enough for EprGroundAtoms because they might interfere with 
	 * quantified literals which don't have the same atom..
	 */
	public Set<EprClause> updateClausesOnSetDpllLiteral(Literal literal) {
		HashSet<EprClause> clauses = 
				this.mDPLLAtomToClauses.get(literal.getAtom());
		if (clauses == null) {
			return null;
		}

		Set<EprClause> unitClauses = new HashSet<EprClause>();
		for (EprClause ec : clauses) {
			EprClauseState newClauseState = 
					ec.updateStateWrtDpllLiteral(literal);

			if (newClauseState == EprClauseState.Conflict) {
				return Collections.singleton(ec);
			} else if (newClauseState == EprClauseState.Unit) {
				unitClauses.add(ec);
			}
		}
		
		if (! unitClauses.isEmpty()) {
			return unitClauses;
		}
		return null;
	}

	/**
	 * Informs the clauses that contain the literal's atom that
	 * it is backtracked by the DPLLEngine.
	 * @param literal
	 */
	public void updateClausesOnBacktrackDpllLiteral(Literal literal) {
		HashSet<EprClause> clauses = 
				this.mDPLLAtomToClauses.get(literal.getAtom());
		if (clauses != null) {
			for (EprClause ec : clauses) {
				ec.backtrackStateWrtDpllLiteral(literal);
			}
		}
	}

	////////////////// 
	////////////////// methods for management of basic data structures
	////////////////// 
	
	public void updateAtomToClauses(DPLLAtom atom, EprClause c) {
		HashSet<EprClause> clauses = mDPLLAtomToClauses.get(atom);
		if (clauses == null) {
			clauses = new HashSet<EprClause>();
			mDPLLAtomToClauses.put(atom, clauses);
		}
		clauses.add(c);
	}

	public void addNewEprPredicate(EprPredicate pred) {
			mAllEprPredicates.add(pred);
	}

	public ScopedHashSet<EprPredicate> getAllEprPredicates() {
			return mAllEprPredicates;
	}

	/**
	 * Add a clause coming from the input script.
	 * @return A ground conflict if adding the given clause directly leads to one.
	 */
	public Clause createEprClause(HashSet<Literal> literals) {
		EprClause newClause = mEprTheory.getEprClauseFactory().getEprClause(literals);
		
		return registerEprClause(newClause);
	}

	/**
	 * Register an eprClause (coming from input or learned) in the corresponding places...
	 * 
	 * Check if it is unit or a conflict.
	 * If it is a conflict immediately resolve it (on the epr decide stack) and return a ground conflict
	 * if the conflict is not resolvable.
	 * If it is unit, queue it for propagation.
	 */
	private Clause registerEprClause(EprClause newClause) {
		mPushStateStack.peek().addClause(newClause);

		for (ClauseLiteral cl : newClause.getLiterals()) {
			updateAtomToClauses(cl.getLiteral().getAtom(), newClause);
		}
		return resolveConflictOrStoreUnits(new HashSet<EprClause>(Collections.singleton(newClause)));
	}
	
	public Iterable<EprClause> getAllEprClauses() {
		return new EprClauseIterable(mPushStateStack);
	}

	//////////////////////////////////// old, perhaps obsolete stuff, from here on downwards /////////////////////////////////////////
	
	/**
	 * Given a substitution and to Term arrays, computes a list of disequalities as follows:
	 * For every position in the two arrays where the substitution needed an equality for unification, adds 
	 *    all the set CCEqualities to the result that are needed for establishing that unifying equality.
	 * @param sub a substitution that unifies terms1 and terms2, possibly with the use of ground equalities
	 * @param terms1 Term array that is unified with terms2 through sub
	 * @param terms2 Term array that is unified with terms1 through sub
	 * @return all the equalities that are currently set through the DPLLEngine 
	 *	         that are needed for the unification of terms1 and terms2
	 */
	@Deprecated
	private ArrayList<Literal> getDisequalityChainsFromSubstitution(TTSubstitution sub, Term[] terms1,
			Term[] terms2) {
		ArrayList<Literal> disequalityChain = new ArrayList<Literal>();
		for (int i = 0; i < terms1.length; i++) {
			if (!(terms1[i] instanceof ApplicationTerm ) || !(terms2[i] instanceof ApplicationTerm)) 
				continue;
			ApplicationTerm pointAt = (ApplicationTerm) terms1[i];
			ApplicationTerm atomAt = (ApplicationTerm)  terms2[i];
			for (CCEquality cceq : sub.getEqPathForEquality(pointAt, atomAt)) {
				disequalityChain.add(cceq.negate());
			}
		}
		return disequalityChain;
	}

	@Deprecated
	public Clause setGroundEquality(CCEquality eq) {
		ApplicationTerm f = (ApplicationTerm) eq.getSMTFormula(mTheory);
		ApplicationTerm lhs = (ApplicationTerm) f.getParameters()[0];
		ApplicationTerm rhs = (ApplicationTerm) f.getParameters()[1];
	
		mEqualityManager.addEquality(lhs, rhs, (CCEquality) eq);
	
		assert false : "TODO: deal with equalities";
		// is there a conflict with currently set points or quantifiedy literals?
//		Clause conflict = checkConsistency();
		
		// possibly update all literal states in clauses, right?..
		//  (..if there is no conflict?..)

//		return conflict;
		return null;
	}
	
	@Deprecated
	public void unsetGroundEquality(CCEquality eq) {
		ApplicationTerm f = (ApplicationTerm) eq.getSMTFormula(mTheory);
		ApplicationTerm lhs = (ApplicationTerm) f.getParameters()[0];
		ApplicationTerm rhs = (ApplicationTerm) f.getParameters()[1];

		mEqualityManager.backtrackEquality(lhs, rhs);
	}
	

	@Deprecated
	public CClosure getCClosure() {
		return mCClosure;
	}

	
	
	///////////////////////////////////////////////////////////
	///////////////////////////////////////////////////////////
	/////// methods used in the complete grounding method
	///////////////////////////////////////////////////////////
	///////////////////////////////////////////////////////////

	public HashSet<EprClause> getAllClauses() {
		HashSet<EprClause> allClauses = new HashSet<EprClause>();
		for (EprPushState es : mPushStateStack) {
			allClauses.addAll(es.getClauses());
		}
		return allClauses;
	}


	public Set<ApplicationTerm> getAllConstants() {
		return mUsedConstants;
	}

	/**
	 * Register constants that occur in the smt-script for tracking.
	 * 
	 * @param constants
	 */
	public void addConstants(HashSet<ApplicationTerm> constants) {
		if (mEprTheory.isGroundAllMode()) {
			HashSet<ApplicationTerm> reallyNewConstants = new HashSet<ApplicationTerm>();
			for (ApplicationTerm newConstant : constants) {
				if (!getAllConstants().contains(newConstant))
					reallyNewConstants.add(newConstant);
			}

			addGroundClausesForNewConstant(reallyNewConstants);
		}
		mUsedConstants.addAll(constants);
	}

	private void addGroundClausesForNewConstant(HashSet<ApplicationTerm> newConstants) {
		ArrayList<Literal[]> groundings = new ArrayList<Literal[]>();
		for (EprClause c : getAllClauses())  {
				groundings.addAll(
						c.computeAllGroundings(
								EprHelpers.getAllInstantiationsForNewConstant(
										c.getVariables(),
										newConstants, 
										this.getAllConstants())));
		}
		addGroundClausesToDPLLEngine(groundings);
	}

	private void addGroundClausesForNewEprClause(EprClause newEprClause) {
		List<Literal[]> groundings = 		
						newEprClause.computeAllGroundings(
								EprHelpers.getAllInstantiations(
										newEprClause.getVariables(),
										this.getAllConstants()));
		addGroundClausesToDPLLEngine(groundings);
	}

	private void addGroundClausesToDPLLEngine(List<Literal[]> groundings) {
		for (Literal[] g : groundings) {
//			//TODO not totally clear if addFormula is the best way, but addClause(..) has
//			//  visibility package right now..
			mEprTheory.getClausifier().getEngine().addFormulaClause(g, null); // TODO: proof (+ hook?)
			
			mLogger.debug("EPRDEBUG (EprStateManager): added ground clause " + Arrays.toString(g));
		}
	}

	/**
	 * at creation of this state manager, we cannot ask the EprTheory for the dawg factory because that
	 * dawgFactory's creation needs the allConstats from this state manager..
	 * @param dawgFactory
	 */
	public void setDawgFactory(DawgFactory<ApplicationTerm, TermVariable> dawgFactory) {
		mDawgFactory = dawgFactory;
	}

	/**
	 * at creation of this state manager, we cannot ask the EprTheory for the clause factory because that
	 * clauseFactory's creation needs the allConstats from this state manager..
	 * @param clauseFactory
	 */
	public void setEprClauseFactory(EprClauseFactory clauseFactory) {
		mEprClauseFactory = clauseFactory;
	}

	public Clause doPropagations() {
		HashSet<EprClause> toProp = new HashSet<EprClause>(mUnitClausesWaitingForPropagation);
		mUnitClausesWaitingForPropagation = new HashSet<EprClause>();
		EprClause conflict = propagateAll(toProp);
		if (conflict == null) {
			return null;
		} else {
			assert conflict.isConflict();
			return resolveConflict(conflict);
		}
	}

	public void registerEprGroundPredicateLiteral(EprGroundPredicateLiteral egpl, Literal l) {
		mLiteralToEprGroundPredicateLiteral.put(l, egpl);
	}

}
