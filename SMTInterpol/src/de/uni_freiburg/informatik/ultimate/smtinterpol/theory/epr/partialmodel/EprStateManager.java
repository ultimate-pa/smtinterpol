package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EqualityManager;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprGroundLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprQuantifiedLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClauseFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClauseState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprBaseClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprClauseOld;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprDerivedClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprGroundUnitClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprNonUnitClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprQuantifiedUnitClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprUnitClause;
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
 * @author nutz
 */
public class EprStateManager {

	private Stack<EprPushState> mPushStateStack = new Stack<EprPushState>();
	
	private ScopedHashSet<ApplicationTerm> mUsedConstants;

	public EqualityManager mEqualityManager;
	private EprTheory mEprTheory;
	private Theory mTheory;
	private CClosure mCClosure;
	
	ScopedHashSet<EprPredicate> mAllEprPredicates = new ScopedHashSet<EprPredicate>();
	
	/**
	 * Remembers for each DPLLAtom in which EprClauses it occurs (if any).
	 */
	HashMap<DPLLAtom, HashSet<EprClause>> mDPLLAtomToClauses = 
			new HashMap<DPLLAtom, HashSet<EprClause>>();

	final private EprClauseFactory mEprClauseFactory;

	final private DawgFactory<ApplicationTerm, TermVariable> mDawgFactory;

	
	public EprStateManager(EprTheory eprTheory) {
		mPushStateStack.add(new EprPushState());

		mEprTheory = eprTheory;
		mEqualityManager =  eprTheory.getEqualityManager();
		mTheory = eprTheory.getTheory();
		mCClosure = eprTheory.getCClosure();
		mEprClauseFactory = eprTheory.getEprClauseFactory();
		mDawgFactory = eprTheory.getDawgFactory();
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

		Set<EprClause> conflictsOrUnits = null;

		while (true) {
			// if there is currently no conflict or unit clause, decide something
			if (conflictsOrUnits == null) {
				// there is no conflict and no unit clause
				
				DecideStackLiteral nextDecision = null;

				nextDecision = isModelComplete();

				if (nextDecision == null) {
					// model is complete
					return null;
				}
				
				// make the decision
				if (nextDecision instanceof DecideStackQuantifiedLiteral) {
					conflictsOrUnits = 
							setEprDecideStackLiteral((DecideStackQuantifiedLiteral) nextDecision);
				} else if (nextDecision instanceof DecideStackGroundLiteral) {
					// if the next requested decision is ground, suggest it to the DPLLEngine, and give 
					// back control to the DPLLEngine
					Literal groundDecision = ((DecideStackGroundLiteral) nextDecision).getLiteral();
					assert groundDecision.getAtom().getDecideStatus() == null : "If this is not the case, then"
							+ "it might be dangerous to return null: if null is returned to computeConflictClause,"
							+ "this means the EprTheory says there is no conflict and I have a full model..";
					mEprTheory.addGroundDecisionSuggestion(groundDecision);
//					mEprTheory.addGroundLiteralToPropagate(nextDecision.);
					return null;
				} else {
					assert false : "should not happen";
				}
			} else {
				// there is a conflict or unit clause

				EprClause nextConflictOrUnit = conflictsOrUnits.iterator().next();

				if (nextConflictOrUnit.isConflict()) {
					// we have conflicts; explain them, learn clauses, return the explained version of the conflicts
					// if there was no decision, return a grounding of the conflict (perhaps several..)
					EprClause unresolvableConflict = resolveConflict(chooseConflictOrUnit(conflictsOrUnits));
					if (unresolvableConflict != null) {
						return chooseGroundingFromConflict(unresolvableConflict);
					}

					conflictsOrUnits = null;
				} else if (nextConflictOrUnit.isUnit()) {
					// if we have a unit clause, propagate the literal
					// the set..-method returns the new set of conflicts or units
					// TODO: should work like this (one unit prop for every iteration),
					//   but is there an unnecessary computation involved when determining the clause states again?
					
					conflictsOrUnits.remove(nextConflictOrUnit);
					
					// one epr unit clause may yield many propagations 
					// --> iteratively set them, if one produces a conflict, go back to the outer epr dpll loop
					//     if one produces more unit propagations, it is ok to just add them to conflictsOrUnits, because we
					//      it contains unit clauses right now..
					Map<ClauseEprQuantifiedLiteral, IDawg<ApplicationTerm, TermVariable>> clToUps = 
							nextConflictOrUnit.getClauseLitToUnitPoints();
					for (Entry<ClauseEprQuantifiedLiteral, IDawg<ApplicationTerm, TermVariable>> en : clToUps.entrySet()) {
						ClauseEprQuantifiedLiteral cl = en.getKey();
						IDawg<ApplicationTerm, TermVariable> dawg = en.getValue();
						DecideStackPropagatedLiteral prop = new DecideStackPropagatedLiteral(
								cl.getPolarity(), 
								cl.getEprPredicate(),
								mDawgFactory.renameColumnsAndRestoreConstants(
										dawg, 
										cl.getTranslationForEprPredicate(), 
										cl.getArgumentsAsObjects(),
										cl.getEprPredicate().getTermVariablesForArguments()),
								cl);

						Set<EprClause> newConflictsOrUnits = setEprDecideStackLiteral(prop);

						if (newConflictsOrUnits != null) {
							if (newConflictsOrUnits.iterator().next().isConflict()) {
								conflictsOrUnits = newConflictsOrUnits;
								break;
							} else if (newConflictsOrUnits.iterator().next().isUnit()) {
								conflictsOrUnits.addAll(newConflictsOrUnits);
								break;
							} else {
								assert false : "should not happen";
							}
						}
					}
					
				} else {
					assert false : "should not happen";
				}
			}
		}
	}
	
	/**
	 * We may have several conflict clause, choose one to resolve.
	 * @param conflictsOrUnits
	 * @return
	 */
	private EprClause chooseConflictOrUnit(Set<EprClause> conflictsOrUnits) {
		return conflictsOrUnits.iterator().next();
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
//	private Clause chooseGroundingFromConflicts(Set<EprClause> conflicts) {
	private Clause chooseGroundingFromConflict(EprClause conflicts) {
		assert false : "TODO: implement";
		return null;
	}

	/**
	 * Resolve the given conflicts, i.e., 
	 *  - backtrack all unit propagations until the last decision 
	 *  - explain the conflict accordingly, possibly learn some clauses
	 *  - return the last decision along with the explanation, so the next decision can be informed by that
	 *  
	 * @param conflicts
	 * @return
	 */
	private EprClause resolveConflict(EprClause conflict) {
		EprClause currentConflict = conflict;
		
		while (true) {
			currentConflict = tryFactoring(currentConflict);
			
			currentConflict = tryBackjumping(currentConflict);
			if (currentConflict == null) {
				return null;
			}

			DecideStackLiteral topMostDecideStackLiteral = popDecideStack();
			if (topMostDecideStackLiteral == null) {
				// we have come to the top of the decide stack --> return the conflict
				return currentConflict;
			}

			// backtrack the literal
			unsetEprDecideStackLiteral((DecideStackDecisionLiteral) topMostDecideStackLiteral);

			if (topMostDecideStackLiteral instanceof DecideStackDecisionLiteral) {
				
				refine(currentConflict);
				return null;

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
	
	private void refine(EprClause currentConflict) {
		// TODO Auto-generated method stub
		
	}

	private void learnClause(EprClause currentConflict) {
		addClause(currentConflict);
	}

	private EprClause tryBackjumping(EprClause currentConflict) {
		assert false : "TODO: implement";
		return null;
	}

	private EprClause tryFactoring(EprClause currentConflict) {
		assert false : "TODO: implement";
		return null;
	}

	private DecideStackQuantifiedLiteral popDecideStack() {
		EprPushState pushStateWithLastDecideStackLiteral = mPushStateStack.peek();
		DecideStackQuantifiedLiteral lit = pushStateWithLastDecideStackLiteral.popDecideStack();
		while (lit == null) {
			pushStateWithLastDecideStackLiteral = mPushStateStack.iterator().next();
			lit = pushStateWithLastDecideStackLiteral.popDecideStack();
		}
		return lit;
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
	private DecideStackQuantifiedLiteral isModelComplete() {
		for (EprPredicate ep : getAllEprPredicates()) {
			DecideStackQuantifiedLiteral decision = ep.getNextDecision();
			if (decision != null) {
				return decision;
			}
		}
		return null;
	}
	
	


	public void push() {
		mPushStateStack.push(new EprPushState());
		mAllEprPredicates.beginScope();
		mUsedConstants.beginScope();
		mEprClauseFactory.push();
	}
	
	public void pop() {
		mPushStateStack.pop();
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
		Object conflict = mPushStateStack.peek().setEprGroundLiteral();

		return null;
	}
	
	public void unsetEprGroundLiteral(Literal literal) {
		mPushStateStack.peek().unsetEprGroundLiteral(literal);
	}
	
	public void setEprClauseLiteral(ClauseLiteral lit) {
		mPushStateStack.peek().setEprClauseLiteral(lit);
	}

	public void unsetEprClauseLiteral(ClauseLiteral lit) {
		mPushStateStack.peek().unsetEprClauseLiteral(lit);
	}

	/**
	 *  - assumes that the given literal is not conflicting with the current model of its EprPredicate
	 *    --> it may however yield a conflict given the current clause set
	 *     if such a conflict exists, it is returned, otherwise null is returned
	 * @param decideStackQuantifiedLiteral
	 * @return 
	 */
	public Set<EprClause> setEprDecideStackLiteral(DecideStackQuantifiedLiteral decideStackQuantifiedLiteral) {
		assert false : "TODO: implement";
		Set<EprClause> conflictsOrPropagations = updateClausesOnSetDecideStackLiteral(decideStackQuantifiedLiteral);
		if (conflictsOrPropagations == null) {
			mPushStateStack.peek().pushDecideStackLiteral(decideStackQuantifiedLiteral);
		}
	    return conflictsOrPropagations;
	}


	public void unsetEprDecideStackLiteral(DecideStackQuantifiedLiteral decideStackQuantifiedLiteral) {
		updateClausesOnBacktrackDecideStackLiteral(decideStackQuantifiedLiteral);
		mPushStateStack.peek().popDecideStackLiteral(decideStackQuantifiedLiteral);
	}

	/**
	 * Ask the clauses what happens if dcideStackQuantifiedLiteral is set.
	 * Returns a conflict that the setting of the literal would induce, null if there is none.
	 * 
	 * @param literalToBeSet
	 * @return an EprClause that is Unit or Conflict if there is one, null otherwise
	 */
	private Set<EprClause> updateClausesOnSetDecideStackLiteral(DecideStackQuantifiedLiteral literalToBeSet) {
		HashMap<EprClause, HashSet<ClauseEprQuantifiedLiteral>> quantifiedOccurences = 
				literalToBeSet.getEprPredicate().getQuantifiedOccurences();
		HashMap<EprClause, HashSet<ClauseEprGroundLiteral>> groundOccurences = 
				literalToBeSet.getEprPredicate().getGroundOccurences();
		assert false : "TODO: deal with groundOccurences";
		
		
		Set<EprClause> unitClauses = new HashSet<EprClause>();
		
		for (Entry<EprClause, HashSet<ClauseEprQuantifiedLiteral>> en : quantifiedOccurences.entrySet()) {
			EprClause eprClause = en.getKey();
			
			EprClauseState newClauseState = 
					eprClause.updateStateWrtDecideStackLiteral(literalToBeSet, en.getValue());

			if (newClauseState == EprClauseState.Conflict) {
				return Collections.singleton(eprClause);
			} else if (newClauseState == EprClauseState.Unit) {
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
	 * @param decideStackQuantifiedLiteral
	 */
	private void updateClausesOnBacktrackDecideStackLiteral(DecideStackQuantifiedLiteral decideStackQuantifiedLiteral) {
		assert false : "TODO: implement";
	}


	/**
	 * Inform all the EprClauses that contain the atom (not only the
	 * literal!) that they have to update their fulfillment state.
	 */
	public void updateClausesOnSetDpllLiteral(Literal literal) {
		HashSet<EprClause> clauses = 
				this.getClausesThatContainAtom(literal.getAtom());
		if (clauses != null) {
			for (EprClause ec : clauses) {
				ec.updateStateWrtDpllLiteral(literal);
			}
		}
	}

	/**
	 * Informs the clauses that contain the literal's atom that
	 * it is backtracked by the DPLLEngine.
	 * @param literal
	 */
	public void updateClausesOnBacktrackDpllLiteral(Literal literal) {
		HashSet<EprClause> clauses = 
				this.getClausesThatContainAtom(literal.getAtom());
		if (clauses != null) {
			for (EprClause ec : clauses) {
				ec.backtrackStateWrtDpllLiteral(literal);
			}
		}
	
	}

	/**
	 * Attempts to complete the current partial model (provided by the decides stack)
	 * for the given EprPredicate.
	 * Returns null in the case of success and a ground conflict clause otherwise;
	 * @param ep
	 * @return
	 */
	public Clause completeModelForEprPred(EprPredicate ep) {
		assert false : "TODO: implement";
		return null;
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

	public HashSet<EprClause> getClausesThatContainAtom(DPLLAtom atom) {
		return mDPLLAtomToClauses.get(atom);
	}


	public void addNewEprPredicate(EprPredicate pred) {
			mAllEprPredicates.add(pred);
	}

	public ScopedHashSet<EprPredicate> getAllEprPredicates() {
			return mAllEprPredicates;
	}

	public void addClause(HashSet<Literal> literals) {
		EprClause newClause = mEprTheory.getEprClauseFactory().getClause(literals);
		addClause(newClause);
	}

	private void addClause(EprClause newClause) {
		mPushStateStack.peek().addClause(newClause);

		for (ClauseLiteral cl : newClause.getLiterals()) {
			updateAtomToClauses(cl.getLiteral().getAtom(), newClause);
		}
	}


	
	public Iterable<EprClause> getAllEprClauses() {
		return new EprClauseIterable(mPushStateStack);
	}


	//////////////////////////////////// old, perhaps obsolete stuff, from here on downwards /////////////////////////////////////////
	

	@Deprecated
	HashMap<Set<Literal>, EprNonUnitClause> mLiteralToClauses = new HashMap<Set<Literal>, EprNonUnitClause>();

	@Deprecated
	private Stack<EprState> mEprStateStack = new Stack<EprState>();
	
	// contains the ground literal currently set by the DPLLEngine for
	// every scope that was created by EprTheory.setLiteral(), and the 
	// word "push" for all push scopes
	// (not used at the moment..)
	private Stack<Object> mLiteralStack = new Stack<Object>();
	
	private EprState baseState;
	


	@Deprecated
	public void beginScope(Object literal) {
		mLiteralStack.push(literal);
		mEprStateStack.push(new EprState(mEprStateStack.peek()));
	}

	/**
	 * Revert everything that followed from setting literal
	 *  - pop the corresponding EprState
	 *  - revert the fulfillability status of the remaining epr-clauses (in lower states)
	 * @param literal
	 */
	@Deprecated
	public void endScope(Object literal) {
		mEprStateStack.pop();
		Object popped = mLiteralStack.pop();
//		assert literal.equals(popped);
	}
	
	


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
	public Clause setQuantifiedLiteralWithExceptions(EprQuantifiedUnitClause eqlwe) {
		mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): setting Quantified literal: " + eqlwe);
		
		mEprStateStack.peek().setQuantifiedLiteralWithExceptions(eqlwe);
		
		//TODO: possibly do a more efficient consistency check
		// i.e. only wrt the currently set literal
		Clause conflict = checkConsistency();
		if (conflict != null) {
			mEprStateStack.peek().unsetQuantifiedLiteralWithExceptions(eqlwe);
		}

		//TODO:
		// possibly update all literal states in clauses, right?..
		return conflict;
	}
	
	@Deprecated
	public Clause setGroundEquality(CCEquality eq) {
		ApplicationTerm f = (ApplicationTerm) eq.getSMTFormula(mTheory);
		ApplicationTerm lhs = (ApplicationTerm) f.getParameters()[0];
		ApplicationTerm rhs = (ApplicationTerm) f.getParameters()[1];
	
		mEqualityManager.addEquality(lhs, rhs, (CCEquality) eq);
	
		// is there a conflict with currently set points or quantifiedy literals?
		Clause conflict = checkConsistency();
		
		//TODO:
		// possibly update all literal states in clauses, right?..
		//  (..if there is no conflict?..)

		return conflict;
	}
	
	@Deprecated
	public void unsetGroundEquality(CCEquality eq) {
		ApplicationTerm f = (ApplicationTerm) eq.getSMTFormula(mTheory);
		ApplicationTerm lhs = (ApplicationTerm) f.getParameters()[0];
		ApplicationTerm rhs = (ApplicationTerm) f.getParameters()[1];

		mEqualityManager.backtrackEquality(lhs, rhs);
	}
	
	/**
	 * Checks for all eprPredicates if their current state is consistent.
	 * The current state means points that are set and quantified literals that are set.
	 * @return conflict clause if there is a conflict, null otherwise
	 */
	@Deprecated
	public Clause checkConsistency() {
		
		//TODO: make sure that i case of a
		
		for (EprPredicate pred : mAllEprPredicates) {
			for (EprQuantifiedUnitClause eqwlePos : getSetLiterals(true, pred)) {
				EprQuantifiedUnitClause arPosUnit = eqwlePos.getFreshAlphaRenamedVersion();
				TermTuple ttPos = arPosUnit.getPredicateAtom().getArgumentsAsTermTuple();
				for (EprQuantifiedUnitClause eqwleNeg : getSetLiterals(false, pred)) {
					TermTuple ttNeg = eqwleNeg.getPredicateAtom().getArgumentsAsTermTuple();
					TTSubstitution sub = ttNeg.match(ttPos, mEqualityManager);
					if (sub != null) {
						return arPosUnit.getExplanation().instantiateClause(null, sub);
					}
				}
				
				for (TermTuple pointNeg : getPoints(false, pred)) {
					TTSubstitution sub = pointNeg.match(ttPos, mEqualityManager);
					if (sub != null) {
						EprClauseOld conflict =  arPosUnit.getExplanation().instantiateClause(null, sub, 
								getDisequalityChainsFromSubstitution(sub, pointNeg.terms, 
										arPosUnit.getPredicateAtom().getArguments()));
						return conflict;
					}
				}
			}
			for (TermTuple pointPos : getPoints(true, pred)) {
				for (EprQuantifiedUnitClause eqwleNeg : getSetLiterals(false, pred)) {
					TermTuple ttNeg = eqwleNeg.getPredicateAtom().getArgumentsAsTermTuple();
					TTSubstitution sub = ttNeg.match(pointPos, mEqualityManager);
					if (sub != null) {
						return eqwleNeg.getExplanation().instantiateClause(null, sub);
					}
				}
				
				for (TermTuple pointNeg : getPoints(false, pred)) {
					TTSubstitution sub = pointNeg.match(pointPos, mEqualityManager);
					if (sub != null) {
						// build conflict clause
						ArrayList<Literal> confLits = new ArrayList<Literal>();

						confLits.addAll(getDisequalityChainsFromSubstitution(sub, pointPos.terms, pointNeg.terms));
						
						confLits.add(pred.getAtomForPoint(pointPos).negate());
						confLits.add(pred.getAtomForPoint(pointNeg));

						return new Clause(confLits.toArray(new Literal[confLits.size()]));
					}
				}
			}
		}

		return null;
	}

	@Deprecated
	public HashSet<TermTuple> getPoints(boolean positive, EprPredicate pred) {
		//TODO: some caching here?
		HashSet<TermTuple> result = new HashSet<TermTuple>();
		for (EprState es : mEprStateStack) {
			EprPredicateModel model = es.mPredicateToModel.get(pred);
			if (model == null) //maybe not all eprStates on the stack know the predicate
				continue;
			if (positive)
				result.addAll(model.mPositivelySetPoints);
			else
				result.addAll(model.mNegativelySetPoints);
		}
		return result;
	}

	@Deprecated
	public ArrayList<EprQuantifiedUnitClause> getSetLiterals(boolean positive, EprPredicate pred) {
		//TODO: some caching here?
		ArrayList<EprQuantifiedUnitClause> result = new ArrayList<EprQuantifiedUnitClause>();
		for (EprState es : mEprStateStack) {
			EprPredicateModel model = es.mPredicateToModel.get(pred);
			if (model == null) //maybe not all eprStates on the stack know the predicate
				continue;
			if (positive)
				result.addAll(model.mPositivelySetQuantifiedLitsWE);
			else
				result.addAll(model.mNegativelySetQuantifiedLitsWE);
		}
		return result;
	
	}

	@Deprecated
	public ArrayList<EprQuantifiedUnitClause> getSetLiterals(EprPredicate eprPredicate) {
		//TODO: some caching here?
		ArrayList<EprQuantifiedUnitClause> result = new ArrayList<EprQuantifiedUnitClause>();
		result.addAll(getSetLiterals(true, eprPredicate));
		result.addAll(getSetLiterals(false, eprPredicate));
		return result;
	}



	/**
	 * Adds a clause that is derivable in the current state.
	 * @param dc
	 */
	@Deprecated
	public boolean addDerivedClause(EprNonUnitClause dc) {
		mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): adding derived clause " + dc);
		return mEprStateStack.peek().addDerivedClause(dc);
	}

	@Deprecated
	public boolean addBaseClause(EprNonUnitClause bc) {
		mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): adding base clause " + bc);

		if (mEprTheory.isGroundAllMode()) {
			addGroundClausesForNewEprClause(bc);
		}

		return mEprStateStack.peek().addBaseClause(bc);
	}

	@Deprecated
	public ArrayList<EprNonUnitClause> getTopLevelDerivedClauses() {
		return mEprStateStack.peek().getDerivedClauses();
	}

	@Deprecated
	public HashSet<EprNonUnitClause> getFulfilledClauses() {
		HashSet<EprNonUnitClause> fulfilledClauses = new HashSet<EprNonUnitClause>();
		for (EprNonUnitClause ec : getAllClauses())
			if (ec.isFulfilled())
				fulfilledClauses.add(ec);
		return fulfilledClauses;
	}
	
	@Deprecated
	public HashSet<EprNonUnitClause> getNotFulfilledClauses() {
		HashSet<EprNonUnitClause> notFulfilledClauses = new HashSet<EprNonUnitClause>();
		for (EprNonUnitClause ec : getAllClauses())
			if (!ec.isFulfilled())
				notFulfilledClauses.add(ec);
		return notFulfilledClauses;
	}

	@Deprecated
	public HashSet<EprClauseOld> getConflictClauses() {
		HashSet<EprClauseOld> result = new HashSet<EprClauseOld>();
		for (EprState es : mEprStateStack) {
			result.addAll(es.getConflictClauses());
		}
		return result;
	}

	/**
	 * makes sure that for the same set of literals only one clause is constructed.
	 * Note that this may return a EprDerivedClause -- if there already is one for the set of Literals
	 */
	@Deprecated
	public EprNonUnitClause getBaseClause(Set<Literal> newLits, Theory theory) {
		EprNonUnitClause result = mLiteralToClauses.get(newLits);
		if (result == null) {
			result = new EprBaseClause(newLits.toArray(new Literal[newLits.size()]), mEprTheory);
			mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): creating new base clause " + result);
			mLiteralToClauses.put(newLits, result);
		}
		return result;
	}
	
	/**
	 * makes sure that for the same set of literals only one clause is constructed.
	 * Note that this may return a EprBaseClause -- if there already is one for the set of Literals
	 */
	@Deprecated
	public EprClauseOld getDerivedClause(Set<Literal> newLits, EprTheory eprTheory, Object explanation) {
		EprNonUnitClause result = mLiteralToClauses.get(newLits);
		if (result == null) {
			result = new EprDerivedClause(newLits.toArray(new Literal[newLits.size()]), eprTheory, explanation);
			mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): creating new derived clause " + result);
			mLiteralToClauses.put(newLits, result);
		}
		return result;
	}

	/**
	 * TODO: rework this some time.
	 * Checks if the given literal is already set, or if something stronger is set.
	 * @param unifiedUnitLiteral
	 * @return
	 */
	@Deprecated
	public boolean isSubsumedInCurrentState(EprUnitClause euc) { //TODO possibly this needs to work on a QuantifiedLitWExcptns
		if (euc instanceof EprGroundUnitClause) {
			Literal lit = ((EprGroundUnitClause) euc).getPredicateLiteral();
			if (lit.getAtom().getDecideStatus() == lit) { // is it set in DPLL?
				return true;
			}
			if (!(lit.getAtom() instanceof EprPredicateAtom))
				return false;

			boolean isPositive = lit.getSign() == 1;
			EprPredicateAtom atom = (EprPredicateAtom) lit.getAtom();

			for (EprQuantifiedUnitClause sl : this.getSetLiterals(isPositive, atom.getEprPredicate())) {
				TermTuple slTT = sl.getFreshAlphaRenamedVersion().getPredicateAtom().getArgumentsAsTermTuple();
				TermTuple tt = atom.getArgumentsAsTermTuple();
				TTSubstitution sub = slTT.match(tt, mEqualityManager);
				if (slTT.isEqualOrMoreGeneralThan(tt))
					return true;
			}
			return false;
		} else {
			assert false : "TODO: implement this case";
			return false;
		}
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

	public HashSet<EprNonUnitClause> getAllClauses() {
		HashSet<EprNonUnitClause> allClauses = new HashSet<EprNonUnitClause>();
		for (EprState es : mEprStateStack) {
			allClauses.addAll(es.getBaseClauses());
			allClauses.addAll(es.getDerivedClauses());
		}
		return allClauses;
	}


	public Set<ApplicationTerm> getAllConstants() {
//		HashSet<ApplicationTerm> result = new HashSet<ApplicationTerm>();
//	
//		for (EprState s : mEprStateStack)
//			result.addAll(s.getUsedConstants());
//		
//		return result;
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
		
//		mEprStateStack.peek().addConstants(constants);
		mUsedConstants.addAll(constants);
	}


	/**
	 * Computes all the instantiations of the variables in freeVars that
	 * are added to the set of instantiations of oldConstants by adding one
	 * or more constants from newConstants.
	 * In other words: compute all instantiations of freeVars where a new constant occurs
	 * at least once.
	 * 
	 * @param freeVars
	 * @param newConstant
	 * @param oldConstants
	 * @return
	 */
	public ArrayList<TTSubstitution> getAllInstantiationsForNewConstant(
			Set<TermVariable> freeVars, 
			Set<ApplicationTerm> newConstants,
			Set<ApplicationTerm> oldConstants) {
		
		ArrayList<TTSubstitution> instsWithNewConstant = 
				new ArrayList<TTSubstitution>();
		ArrayList<TTSubstitution> instsWithOutNewConstant = 
				new ArrayList<TTSubstitution>();
		
		HashSet<ApplicationTerm> allConstants = new HashSet<ApplicationTerm>(oldConstants);
		allConstants.addAll(newConstants);

		instsWithNewConstant.add(new TTSubstitution());
		instsWithOutNewConstant.add(new TTSubstitution());

		for (TermVariable tv : freeVars) {
			ArrayList<TTSubstitution> instsNewWNC = new ArrayList<TTSubstitution>();
			ArrayList<TTSubstitution> instsNewWONC = new ArrayList<TTSubstitution>();
			for (TTSubstitution sub : instsWithNewConstant) {
				for (ApplicationTerm con : allConstants) {
					if (con.getSort().equals(tv.getSort())) {
						TTSubstitution newSub = new TTSubstitution(sub);
						newSub.addSubs(con, tv);
						instsNewWNC.add(newSub);
					}
				}
			}

			for (TTSubstitution sub : instsWithOutNewConstant) {
				for (ApplicationTerm con : oldConstants) {
					if (con.getSort().equals(tv.getSort())) {
						TTSubstitution newSub = new TTSubstitution(sub);
						newSub.addSubs(con, tv);
						instsNewWONC.add(newSub);
					}
				}
				for (ApplicationTerm newConstant : newConstants) {
					if (newConstant.getSort().equals(tv.getSort())) {
						TTSubstitution newSub = new TTSubstitution(sub);
						newSub.addSubs(newConstant, tv);
						instsNewWNC.add(newSub);
					}
				}
			}
			instsWithNewConstant = instsNewWNC;
			instsWithOutNewConstant = instsNewWONC;
		}
		return instsWithNewConstant;
	}

	public ArrayList<TTSubstitution> getAllInstantiations(
			Set<TermVariable> freeVars, 
			Set<ApplicationTerm> constants) {
		ArrayList<TTSubstitution> insts = new ArrayList<TTSubstitution>();
		insts.add(new TTSubstitution());

		for (TermVariable tv : freeVars) {
			ArrayList<TTSubstitution> instsNew = new ArrayList<TTSubstitution>();
			for (TTSubstitution sub : insts) {
				for (ApplicationTerm con : constants) {
					if (con.getSort().equals(tv.getSort())) {
						TTSubstitution newSub = new TTSubstitution(sub);
						newSub.addSubs(con, tv);
						instsNew.add(newSub);
					}
				}
			}
			insts = instsNew;
		}
		return insts;
	}
	
	private void addGroundClausesForNewConstant(HashSet<ApplicationTerm> newConstants) {
		ArrayList<Literal[]> groundings = new ArrayList<Literal[]>();
		for (EprNonUnitClause c : getAllClauses())  {
				groundings.addAll(
						c.computeAllGroundings(
								getAllInstantiationsForNewConstant(
										c.getFreeVars(), 
										newConstants, 
										this.getAllConstants())));
		}
		addGroundClausesToDPLLEngine(groundings);
	}

	private void addGroundClausesForNewEprClause(EprNonUnitClause newEprClause) {
		List<Literal[]> groundings = 		
						newEprClause.computeAllGroundings(
								getAllInstantiations(
										newEprClause.getFreeVars(), 
										this.getAllConstants()));
		addGroundClausesToDPLLEngine(groundings);
	}

	private void addGroundClausesToDPLLEngine(List<Literal[]> groundings) {
		for (Literal[] g : groundings) {
//			//TODO not totally clear if addFormula is the best way, but addClause(..) has
//			//  visibility package right now..
			mEprTheory.getClausifier().getEngine().addFormulaClause(g, null); // TODO: proof (+ hook?)
			
			mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): added ground clause " + Arrays.toString(g));
		}
	}

}
