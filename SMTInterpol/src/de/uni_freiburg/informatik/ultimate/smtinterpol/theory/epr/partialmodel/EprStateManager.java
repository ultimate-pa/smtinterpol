/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprEqualityPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheorySettings;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EqualityManager;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClauseFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClauseManager;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
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


	public final EqualityManager mEqualityManager;
	private final EprTheory mEprTheory;
	private final Theory mTheory;
	private final CClosure mCClosure;
	private final LogProxy mLogger;
	
	private final ScopedHashSet<EprPredicate> mAllEprPredicates = new ScopedHashSet<EprPredicate>();
	
	private final DecideStackManager mDecideStackManager;

	private final EprClauseFactory mEprClauseFactory;

	private final DawgFactory<ApplicationTerm, TermVariable> mDawgFactory;


	private HashMap<Literal, EprGroundPredicateLiteral> mLiteralToEprGroundPredicateLiteral = 
			new HashMap<Literal, EprGroundPredicateLiteral>();


	private EprClauseManager mEprClauseManager;

	/**
	 * All the sorts that we currently track constants of.
	 */
	final ScopedHashSet<Sort> mKnownSorts = new ScopedHashSet<Sort>();
	
	public EprStateManager(EprTheory eprTheory, DawgFactory<ApplicationTerm, TermVariable> dawgFactory, EprClauseFactory clauseFactory) {
		mEprTheory = eprTheory;
		mEqualityManager =  eprTheory.getEqualityManager();
		mTheory = eprTheory.getTheory();
		mCClosure = eprTheory.getCClosure();
		mLogger = eprTheory.getLogger();
		mDecideStackManager = new DecideStackManager(mLogger, eprTheory, this);
		mEprClauseManager = new EprClauseManager(mEprTheory);
		mEprClauseFactory = clauseFactory;
		mDawgFactory = dawgFactory;
	}
	
	public void push() {
		mEprClauseManager.push();
		mDecideStackManager.push();
		mAllEprPredicates.beginScope();
		mDawgFactory.push();
		mEprClauseFactory.push();
		mKnownSorts.beginScope();
	}

	public void pop() {
		mEprClauseManager.pop();
		mDecideStackManager.pop();
		mAllEprPredicates.endScope();
		mDawgFactory.pop();
		mEprClauseFactory.pop();
		mKnownSorts.endScope();
	}

	public void addNewEprPredicate(EprPredicate pred) {
		mAllEprPredicates.add(pred);

		for (Sort pSort : pred.getFunctionSymbol().getParameterSorts()) {
			registerSort(pSort);
		}

		if (!(pred instanceof EprEqualityPredicate)) {
			createCongruenceClauseForPredicate(pred);
		}
	}

	/**
	 * Should be called whenever we see an EprPredicate the first time.
	 * For an EprPredicate P with arity n, introduces the congruence axiom
	 *  { x1 != y1, ..., xn != yn, not P x1 ... xn, P y1 ... yn }
	 *   
	 * 
	 * @param pred
	 * @throws AssertionError
	 */
	private void createCongruenceClauseForPredicate(EprPredicate pred) throws AssertionError {
		/*
		 * add congruence axioms for this predicate
		 */
		final Set<Literal> literalsForCongruenceClause = new HashSet<Literal>();
		
		/*
		 *  create disequalities xi != yi for i in { 1, ..., n } (n = arity)
		 */
		final TermVariable[] leftVariables = new TermVariable[pred.getArity()];
		final TermVariable[] rightVariables = new TermVariable[pred.getArity()];
		final ApplicationTerm[] equalities = new ApplicationTerm[pred.getArity()];
		for (int i = 0; i < pred.getArity(); i++) {
			leftVariables[i] = mTheory.createFreshTermVariable("congVarX", pred.getSorts()[i]);
			rightVariables[i] = mTheory.createFreshTermVariable("congVarY", pred.getSorts()[i]);
			equalities[i] = mTheory.term("=", leftVariables[i], rightVariables[i]);
		}

		for (ApplicationTerm eq : equalities) {
			literalsForCongruenceClause.add(mEprTheory.getEprAtom(eq, 
					0,  //TODO hash
					mEprTheory.getClausifier().getStackLevel()).negate());
		}
		
		// create atoms not P(x1, ..., xn) and P(y1, ..., yn)
		final EprPredicateAtom leftAtom = pred.getAtomForTermTuple(new TermTuple(leftVariables), mTheory, 
				mEprTheory.getClausifier().getStackLevel());
		literalsForCongruenceClause.add(leftAtom.negate());
		
		final EprPredicateAtom rightAtom = pred.getAtomForTermTuple(new TermTuple(rightVariables), mTheory, 
				mEprTheory.getClausifier().getStackLevel());
		literalsForCongruenceClause.add(rightAtom);
		
		// create the clause expressing congruence
		Clause groundConflict = mEprClauseManager.createEprClause(literalsForCongruenceClause);
		if (groundConflict != null) {
			throw new AssertionError("TODO: deal with this case");
		}
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
			final DslBuilder nextDecision = mDecideStackManager.getNextDecision();
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

		mDecideStackManager.popOnBacktrackLiteral(literal);

		EprGroundPredicateLiteral egpl = mLiteralToEprGroundPredicateLiteral.get(literal);
		assert egpl != null;
		egpl.unregister();
		mDecideStackManager.popReasonsOnBacktrackEprGroundLiteral(egpl);
		mEprClauseManager.updateClausesOnBacktrackDpllLiteral(literal);
	}

	/**
	 * Set a literal from another theory, or a boolean constant.
	 *   -- The EprTheory needs to track those because they might occur in EprClauses.
	 * 
	 * @param literal
	 * @return
	 */
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

//	public Set<ApplicationTerm> getAllConstants() {
//		return mDawgFactory.getAllConstants();
//	}

	/**
	 * Register constants that occur in the smt-script for tracking.
	 * 
	 * @param constants
	 */
	public void addConstants(HashSet<ApplicationTerm> constants) {
		if (EprTheorySettings.FullInstatiationMode) {
			HashSet<ApplicationTerm> reallyNewConstants = new HashSet<ApplicationTerm>();
			for (ApplicationTerm newConstant : constants) {
				if (!mDawgFactory.getAllConstants(newConstant.getSort().getRealSort()).contains(newConstant))
					reallyNewConstants.add(newConstant);
			}
	
			addGroundClausesForNewConstant(reallyNewConstants);
		}
		mLogger.debug("EPRDEBUG: (EprStateManager): adding constants " + constants);

//		mDawgFactory.addConstants(constants);
		for (ApplicationTerm constant : constants) {
			Sort sort = constant.getSort().getRealSort();
			registerSort(sort);
			mDawgFactory.addConstant(sort, constant);
		}
	}
	
	private void registerSort(Sort sort) {
		final boolean alreadyPresent = !mKnownSorts.add(sort);
		if (!alreadyPresent) {
			mDawgFactory.addConstant(sort, createDefaultConstant(sort));
		}
		assert allKnownSortsAreRealSorts(mKnownSorts);
	}

	private boolean allKnownSortsAreRealSorts(ScopedHashSet<Sort> knownSorts) {
		for (Sort ks : knownSorts) {
			if (ks != ks.getRealSort()) {
				return false;
			}
		}
		return true;
	}

	private ApplicationTerm createDefaultConstant(Sort sort) {
		final FunctionSymbol fs = mTheory.declareFunction(
					"(defaultConstant)", new Sort[0], sort);
		final ApplicationTerm defaultTerm = mTheory.term(fs);
		return defaultTerm;
	}

	private void addGroundClausesForNewConstant(HashSet<ApplicationTerm> newConstants) {
		ArrayList<Literal[]> groundings = new ArrayList<Literal[]>();
		for (EprClause c : mEprClauseManager.getAllClauses())  {
			assert false : "TODO: restore below code"; // TODO
//				groundings.addAll(
//						c.computeAllGroundings(
//								EprHelpers.getAllInstantiationsForNewConstant(
//										c.getVariables(),
//										newConstants, 
//										this.getAllConstants())));
		}
		addGroundClausesToDPLLEngine(groundings);
	}

	private void addGroundClausesForNewEprClause(EprClause newEprClause) {
		assert false : "TODO: restore below code"; // TODO
//		List<Literal[]> groundings = 		
//						newEprClause.computeAllGroundings(
//								EprHelpers.getAllInstantiations(
//										newEprClause.getVariables(),
//										this.getAllConstants()));
//		addGroundClausesToDPLLEngine(groundings);
	}

	private void addGroundClausesToDPLLEngine(List<Literal[]> groundings) {
			for (Literal[] g : groundings) {
	//			//TODO not totally clear if addFormula is the best way, but addClause(..) has
	//			//  visibility package right now..
				mEprTheory.getClausifier().getEngine().addFormulaClause(g, null); // TODO: proof (+ hook?)
				
				mLogger.debug("EPRDEBUG (EprStateManager): added ground clause " + Arrays.toString(g));
			}
		}

//	/**
//	 * at creation of this state manager, we cannot ask the EprTheory for the clause factory because that
//	 * clauseFactory's creation needs the allConstats from this state manager..
//	 * @param clauseFactory
//	 */
//	public void setEprClauseFactory(EprClauseFactory clauseFactory) {
//		mEprClauseFactory = clauseFactory;
//	}

	

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
		// TODO: as is, this method seems weird, architecture-wise
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
