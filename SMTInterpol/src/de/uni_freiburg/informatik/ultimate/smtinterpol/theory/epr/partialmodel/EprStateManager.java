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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprGroundLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprQuantifiedLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClauseFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClauseManager;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClauseState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.UnitPropagationData;
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

	private ScopedHashSet<ApplicationTerm> mUsedConstants = new ScopedHashSet<ApplicationTerm>();

	public EqualityManager mEqualityManager;
	private EprTheory mEprTheory;
	private Theory mTheory;
	private CClosure mCClosure;
	private LogProxy mLogger;
	
	ScopedHashSet<EprPredicate> mAllEprPredicates = new ScopedHashSet<EprPredicate>();
	
	private final DecideStackManager mDecideStackManager;

	private EprClauseFactory mEprClauseFactory;

	private DawgFactory<ApplicationTerm, TermVariable> mDawgFactory;


	private HashMap<Literal, EprGroundPredicateLiteral> mLiteralToEprGroundPredicateLiteral = 
			new HashMap<Literal, EprGroundPredicateLiteral>();


	private EprClauseManager mEprClauseManager;
	
	public EprStateManager(EprTheory eprTheory) {
		mEprTheory = eprTheory;
		mEqualityManager =  eprTheory.getEqualityManager();
		mTheory = eprTheory.getTheory();
		mCClosure = eprTheory.getCClosure();
		mEprClauseFactory = eprTheory.getEprClauseFactory();
		mLogger = eprTheory.getLogger();
		mDecideStackManager = new DecideStackManager(mLogger, eprTheory, this);
		mEprClauseManager = new EprClauseManager(mEprTheory);
	}
	
	public void push() {
		mEprClauseManager.push();
		mDecideStackManager.push();
		mAllEprPredicates.beginScope();
		mUsedConstants.beginScope();
		mEprClauseFactory.push();
	}

	public void pop() {
		mEprClauseManager.pop();
		mDecideStackManager.pop();
		mAllEprPredicates.endScope();
		mUsedConstants.endScope();
		mEprClauseFactory.pop();
	}

	public void addNewEprPredicate(EprPredicate pred) {
			mAllEprPredicates.add(pred);
	}

	public void registerEprGroundPredicateLiteral(EprGroundPredicateLiteral egpl, Literal l) {
		mLiteralToEprGroundPredicateLiteral.put(l, egpl);
	}

	public Clause doPropagations() {
		return mDecideStackManager.doPropagations();
		
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
	
			DslBuilder nextDecision = mDecideStackManager.getNextDecision();
			if (nextDecision == null) {
				// model is complete
				return null;
			}
	
			// make the decision
			if (!nextDecision.isOnePoint()) {
				Set<EprClause> conflictsOrUnits = mDecideStackManager.pushEprDecideStack(nextDecision);
				return mDecideStackManager.resolveConflictOrStoreUnits(conflictsOrUnits);
			} else {
				// if the next requested decision is ground, suggest it to the DPLLEngine, and give 
				// back control to the DPLLEngine
				Literal groundDecision = nextDecision.getEprPredicate()
						.getAtomForTermTuple(
								new TermTuple(
										nextDecision.getPoint().toArray(new ApplicationTerm[nextDecision.getPoint().size()])), // TODO: make nicer
								mTheory, 
								mEprTheory.getClausifier().getStackLevel());
				assert groundDecision.getAtom().getDecideStatus() == null : "If this is not the case, then"
						+ "it might be dangerous to return null: if null is returned to computeConflictClause,"
						+ "this means the EprTheory says there is no conflict and I have a full model..";
				mEprTheory.addGroundDecisionSuggestion(groundDecision);
				return null;
			}
		}
	}

	/**
	 * Update the state of the epr solver according to a ground epr literal being set.
	 * This entails
	 *  - updating the decide stack --> EDIT: .. not, the ground decide stack is managed by the DPLLEngine
	 *  - triggering updates of clause states for the right clauses (maybe somewhere else..)
	 * @param literal
	 * @return
	 */
	public Clause setEprGroundLiteral(Literal literal) {
		// the main difference to a non-epr ground literal is that this literal may interact with the epr decide stack
		//   thus we have to check for contradictions before calling update... (which assumes consistency of the "set points" for each clauseliteral)
		//   after that we treat it like a decide stack literal (again because of the interactions with other literals over epr predicates)
		
		EprGroundPredicateLiteral egpl = new EprGroundPredicateLiteral(literal, mDawgFactory, this);
		
		DecideStackLiteral conflictingDsl = mDecideStackManager.searchConflictingDecideStackLiteral(egpl);
		
		if (conflictingDsl != null) {
			Clause unresolvableGroundConflict = mDecideStackManager.resolveDecideStackInconsistency(egpl, conflictingDsl);
			if (unresolvableGroundConflict != null) {
				// setting literal resulted in a conflict that cannot be resolved by reverting epr decisions
				return unresolvableGroundConflict;
			}
		}
	
		mDecideStackManager.pushOnSetLiteral(literal);
		Set<EprClause> confOrUnits = mEprClauseManager.updateClausesOnSetEprLiteral(egpl);
		return mDecideStackManager.resolveConflictOrStoreUnits(confOrUnits);
	}

	public void unsetEprGroundLiteral(Literal literal) {
		assert literal.getAtom() instanceof EprGroundPredicateAtom;

		EprGroundPredicateLiteral egpl = mLiteralToEprGroundPredicateLiteral.get(literal);
		assert egpl != null;
		EprPredicate pred = egpl.getEprPredicate();
		egpl.unregister();
		mDecideStackManager.popOnBacktrackLiteral(literal);
		mEprClauseManager.updateClausesOnBacktrackDpllLiteral(literal);
		
//		/*
//		 * The backtracked literal may still follow from something on the epr decide stack
//		 *  --> in that case we immediately propagate it "back" to the dpll engine
//		 */
//		for (IEprLiteral el : pred.getEprLiterals()) {
//			if (el instanceof EprGroundPredicateLiteral) {
//				assert el != egpl : "we just backtracked the literal " + el + " it should have been unregistered";
//				continue;
//			}
//			EprClause conflict = mEprTheory.getStateManager().setGroundAtomIfCoveredByDecideStackLiteral(
//					(DecideStackLiteral) el, (EprGroundPredicateAtom) literal.getAtom());
//			assert conflict == null : literal + " was just backtracked -- so there should not be a conflict, right?..";
//		}
	}

	public Clause setDpllLiteral(Literal literal) {
		mDecideStackManager.pushOnSetLiteral(literal);
		Set<EprClause> conflictOrUnits = mEprClauseManager.updateClausesOnSetDpllLiteral(literal);
		return mDecideStackManager.resolveConflictOrStoreUnits(conflictOrUnits);
	}

	public void unsetDpllLiteral(Literal literal) {
		mDecideStackManager.popOnBacktrackLiteral(literal);
		mEprClauseManager.updateClausesOnBacktrackDpllLiteral(literal);
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
		mLogger.debug("EPRDEBUG: (EprStateManager): adding constants " + constants);
		mUsedConstants.addAll(constants);
	}

	private void addGroundClausesForNewConstant(HashSet<ApplicationTerm> newConstants) {
		ArrayList<Literal[]> groundings = new ArrayList<Literal[]>();
		for (EprClause c : mEprClauseManager.getAllClauses())  {
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
			// the decide stack literal does not talk about the atom
			return null;
		}
		
		if (atom.getDecideStatus() == null) {
			// the atom is undecided in the DPLLEngine
			// --> propagate or suggest it
			
			Literal groundLiteral = dsl.getPolarity() ?	atom : atom.negate();
			if (mDecideStackManager.isDecisionLevel0()) {
				DecideStackPropagatedLiteral dspl = (DecideStackPropagatedLiteral) dsl;
				Clause reasonGroundUnitClause =
						dspl.getReasonClauseLit()
							.getGroundingForGroundLiteral(dspl.getClauseDawg(), groundLiteral);
				mLogger.debug("EPRDEBUG: EprStateManager.setGroundAtomIfCovered..");
				mEprTheory.addGroundLiteralToPropagate(
						groundLiteral, 
						reasonGroundUnitClause);
			} else {
				// there is at least one decision on the epr decide stack
				// --> the current dsl's decisions may not be forced by the DPLLEngines decide state 
				// --> suggest to the DPLLEngine to set the literal the same way
				mEprTheory.addGroundDecisionSuggestion(groundLiteral);
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

	public void learnClause(EprClause clauseToLearn) {
		// TODO: as is this method seems weird, architecture-wise
		// the registration has to be done for any epr clause that we add to our formula
		// --> just ditch this method, use register.. instead??

		mEprTheory.getLogger().debug("EPRDEBUG: (EprClauseManager) learning new EprClause: " + clauseToLearn);

		mEprClauseManager.registerEprClause(clauseToLearn);
	}

	public ScopedHashSet<EprPredicate> getAllEprPredicates() {
			return mAllEprPredicates;
	}

	public EprClauseManager getEprClauseManager() {
		return mEprClauseManager;
	}

	public DecideStackManager getDecideStackManager() {
		return mDecideStackManager;
	}
}
