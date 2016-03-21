package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashSet;

public class EprTheory implements ITheory {


//	SimpleList<Clause> mEprClauses = new SimpleList<>(); //cant have a SimpleList instersecting with others..
	

	//we keep updated lists of EprClauses that are fulfilled in the current decision state
	// typically an EprClause would be fulfilled when one of its non-quantified-Epr-literals is set to "true" 
	// through setLiteral
	// TODO: probably should do something more efficient

	//TODO: replace arraylist, simplelist made problems..
//	ArrayList<Clause> mEprClauses = new ArrayList<>();
//	ArrayList<Clause> mFulfilledEprClauses = new ArrayList<>();
//	ArrayList<Clause> mNotFulfilledEprClauses = new ArrayList<>();
	HashSet<EprClause> mEprClauses = new HashSet<>();
	HashSet<Clause> mFulfilledEprClauses = new HashSet<>();
	HashSet<Clause> mNotFulfilledEprClauses = new HashSet<>();
	
	int mClauseCounter = 0;

//	ArrayList<EprClause> mEprUnitClauses = new ArrayList<>();
//	SimpleList<Clause> mFulfilledEprClauses = new SimpleList<>();
//	SimpleList<Clause> mNotFulfilledEprClauses = new SimpleList<>();
	
	HashMap<FunctionSymbol, EprPredicate> mFunctionSymbolToEprPredicate = new HashMap<>();

	HashMap<Literal, HashSet<EprClause>> mLiteralToClauses = new HashMap<Literal, HashSet<EprClause>>();
	
	ArrayDeque<Literal> mGroundLiteralsToPropagate = new ArrayDeque<Literal>();

	private Theory mTheory;
	private DPLLEngine mEngine;

	HashMap<Object, HashMap<TermVariable, Term>> mBuildClauseToAlphaRenamingSub = 
			new HashMap<Object, HashMap<TermVariable,Term>>();
	
	EprStateManager mEprStateManager;

	private HashMap<Literal, Clause> mPropLitToExplanation = new HashMap<>();

	//	private Term mAlmostAllConstant;
//	
	public EprTheory(Theory th, DPLLEngine engine) {
		mTheory = th;
		mEngine = engine;

		mEprStateManager = new EprStateManager();
	}

	@Override
	public Clause startCheck() {
//		throw new UnsupportedOperationException();
		// TODO Auto-generated method stub
		System.out.println("EPRDEBUG: startCheck");
		return null;
	}

	@Override
	public void endCheck() {
		// TODO Auto-generated method stub

//		throw new UnsupportedOperationException();
		System.out.println("EPRDEBUG: endCheck");
	}

	@Override
	public Clause setLiteral(Literal literal) {
		System.out.println("EPRDEBUG: setLiteral " + literal);
		
		mEprStateManager.beginScope(literal);

		// does this literal occur in any of the EprClauses?
		// --> then check for satisfiability
		//   return a conflict clause in case
		//   possibly do (or cache) propagations
		// --> otherwise update the predicate model (held in the corresponding EprPredicate) accordingly

		DPLLAtom atom = literal.getAtom();
		
		if (atom instanceof EprGroundPredicateAtom) {
			// literal is of the form (P c1 .. cn) (no quantification, but an EprPredicate)
			// it being set by the DPLLEngine (the quantified EprPredicateAtoms are not known to the DPLLEngine)
			

			//current Arbeitsteilung concerning EprTheory solver state information:
			// EprStateManager deals with 
			//  - single points in the predicates
			//  - which clauses are derived clauses at which level
			//  - which quantified literals (with exceptions) are set
			// EprTheory deals with EprClauses, i.e.:
			//  - updates the fulfillabilityState of all currently active clauses' literals
			//  - updates its own set of currently active clauses (derived or not) with help of the EprStateManager

			EprClause conflict = mEprStateManager.setGroundLiteral(literal);
			if (conflict != null)
				return conflict; // then act as if the literal is not set, right?

//			updateClauseQuantifiedLiteralFulfillabilityOnPointSetting(literal);
			for (EprClause ec : mEprClauses)
				ec.setGroundLiteral(literal);

			return null;
		} else if (atom instanceof EprEqualityAtom 
				|| atom instanceof EprQuantifiedPredicateAtom) {
			//this should not happen because an EprEqualityAtom always has at least one
			// quantified variable, thus the DPLLEngine should not know about that atom
			assert false : "DPLLEngine is setting a quantified EprAtom --> this cannot be..";
			return null;
		} else {
			// not an EprAtom 
			// --> check if it occurs in one of the EPR-clauses
			//      if it fulfills the clause, mark the clause as fulfilled
			//      otherwise do nothing, because the literal means nothing to EPR 
			//          --> other theories may report their own conflicts..?
			// (like standard DPLL)
			
			for (EprClause ec : mLiteralToClauses.get(literal)) {
				ec.setGroundLiteral(literal);
				updateFulFilledSets(ec);
			}

			System.out.println("EPRDEBUG: setLiteral, new fulfilled clauses: " + mFulfilledEprClauses);
			System.out.println("EPRDEBUG: setLiteral, new not fulfilled clauses: " + mNotFulfilledEprClauses);

			return null;
		}
	}
	
//	/**
//	 * Called when a point is set.
//	 * Checks for each epr-clause if setting that point contradicts a quantified literal in the clause. 
//	 * Updates that clause's status accordingly.
//	 * @param settingPositive is true if this method was called because atom is being set positive, negative if atom is being
//	 *  set negative
//	 * @param atom
//	 */
//	private void updateClauseQuantifiedLiteralFulfillabilityOnPointSetting(Literal groundLit) {
////			boolean settingPositive, TermTuple point, EprPredicate pred) {
//		boolean settingPositive = groundLit.getSign() == 1;
//		EprGroundPredicateAtom egpa = (EprGroundPredicateAtom) groundLit.getAtom();
//		TermTuple point = egpa.getArgumentsAsTermTuple(); 
//		EprPredicate pred = egpa.eprPredicate; 
//
//		for (Entry<EprClause, HashSet<Literal>> qo : pred.mQuantifiedOccurences.entrySet()) {
//			EprClause clause = qo.getKey();
//			for (Literal quantifiedLit : qo.getValue()) {
//				boolean oppositeSigns = (quantifiedLit.getSign() == 1) ^ settingPositive;
//				TermTuple otherPoint = new TermTuple(((EprPredicateAtom) quantifiedLit.getAtom()).getArguments());
//				HashMap<TermVariable, Term> subs = point.match(otherPoint);
//				if (oppositeSigns && subs != null) {
//					clause.setQuantifiedLiteralUnfulfillable(quantifiedLit, groundLit);
//				}
//			}
//		}
//	}

	private void updateFulFilledSets(EprClause ec) {
		if (!ec.isFulfilled() && mFulfilledEprClauses.contains(ec)) {
			mFulfilledEprClauses.remove(ec);
			mNotFulfilledEprClauses.add(ec);
		} else if (ec.isFulfilled() && mNotFulfilledEprClauses.contains(ec)) {
			mNotFulfilledEprClauses.remove(ec);
			mFulfilledEprClauses.add(ec);
		}
	}

	@Override
	public void backtrackLiteral(Literal literal) {
		System.out.println("EPRDEBUG: backtrackLiteral");
		// .. dual to setLiteral
		
		backtrackEprState(literal);

		// update the fulfillment states of the remaining clauses
		DPLLAtom atom = literal.getAtom();
		if (atom instanceof EprGroundPredicateAtom) {
			// literal is of the form (P x1 .. xn)
			for (EprClause ec : mEprClauses)
				ec.unsetGroundLiteral(literal);

		} else if (atom instanceof EprEqualityAtom
				|| atom instanceof EprQuantifiedPredicateAtom) {
			assert false : "DPLLEngine is unsetting a quantified EprAtom --> this cannot be..";
		} else {
			// not an EprAtom 
			for (EprClause ec : mEprClauses)
				ec.unsetGroundLiteral(literal);

		}
		System.out.println("EPRDEBUG: backtrackLiteral, new fulfilled clauses: " + mFulfilledEprClauses);
		System.out.println("EPRDEBUG: backtrackLiteral, new not fulfilled clauses: " + mNotFulfilledEprClauses);
	}

	/**
	 * Pop the EprStateStack, remove the derived clauses from the sets of clauses managed by the theory.
	 * @param literal
	 */
	private void backtrackEprState(Literal literal) {
		mFulfilledEprClauses.removeAll(mEprStateManager.getTopLevelDerivedClauses());
		mNotFulfilledEprClauses.removeAll(mEprStateManager.getTopLevelDerivedClauses());
		mEprClauses.removeAll(mEprStateManager.getTopLevelDerivedClauses());
		mEprStateManager.endScope(literal);
	}



	@Override
	public Clause checkpoint() {
		System.out.println("EPRDEBUG: checkpoint");
		
		EprClause conflict = null;
		
		conflict = eprPropagate();
	
		
		///////////////// old begin ////////////
		//plan:
		// for each epr clause c
		//  if c is already fulfilled: skip
		//  else:
		//   collect the the positive EprEqualityAtoms 
		//             (there are no negative ones, because destructive equality reasoning eliminated them) 
		//   for each EprPredicateAtom epa:
		//    look up if in the current state (setLiteral stuff) there is a contradiction with epa
		//   if all epa had a contradiction:
		//    return the conflicting points as conflict clause
		// if no clause yielded a conflict:
		//  return null
		

//		boolean checkResult = true;
		
//		for (Clause c : mNotFulfilledEprClauses) {
//			EprClause eprClause = (EprClause)	c;
//			
//			// an epr clause looks like this:
//			// x1 =/!= x2 \/ ... \/ xn+1 = c1 ... \/ (P1 ci/xi ... cj/xj) \/ ... \/ (non-EPR literals)
//			// we have
//			// - (dis)equalities over two quantified variables
//			// - equalities over a quantified variable and a constant each
//			// - predicates over quantified variables and/or constants
//			// - non-epr literals (in mNotFulfilledEprClauses, they are all false (maybe unset??))
//			Clause conflict = eprClause.check();
////			checkResult &= conflict == null;
//			if (conflict != null)
//				return conflict;
//		}
		///////////////// old end ////////////
		
//		return null;
		return conflict;
	}

	/**
	 * Does/queues all propagations that can be made through unit clause ec
	 * @param ec a unit clause (i.e., unit in the current solver state)
	 */
	private EprClause eprPropagate() {
		EprClause conflict = null;

		HashSet<Clause> notFulfilledCopy = new HashSet<>(mNotFulfilledEprClauses);
		//unit propagation
		for (Clause c : notFulfilledCopy) {
			EprClause ec = (EprClause) c;
			Literal unitLiteral = ec.getUnitClauseLiteral();
//			if (!(unitLiteral.getAtom() instanceof EprQuantifiedPredicateAtom))
//				mEngine.addAtom(unitLiteral.getAtom());

			if (unitLiteral != null) {
				System.out.println("EPRDEBUG: found unit clause: " + ec);

				if (unitLiteral.getAtom() instanceof EprQuantifiedPredicateAtom) {
					EprQuantifiedLitWExcptns eqlwe = new EprQuantifiedLitWExcptns(
							unitLiteral.getSign() == 1, 
							(EprQuantifiedPredicateAtom) unitLiteral.getAtom(), 
							ec.mExceptedPoints, 
							ec);
					conflict = setQuantifiedAtom(eqlwe);
				} else {
					/*
					 * either an EprGroundAtom or a non EprAtom
					 * (plan atm: don't propagate EprEqualities)
					 * --> just propagate the literal through the normal means
					 */
					mEngine.addAtom(unitLiteral.getAtom());
					mPropLitToExplanation.put(unitLiteral, ec.getInstantiationOfClauseForCurrentUnitLiteral());
					mGroundLiteralsToPropagate.add(unitLiteral);
				}
			}
		}
		
		
		return conflict;
	}

	private EprClause setQuantifiedAtom(EprQuantifiedLitWExcptns eqlwe) {
		
		EprClause conflict = null;

		mEprStateManager.setQuantifiedLiteralWithExceptions(eqlwe);
		
		/*
		 * propagate a quantified predicate
		 *  --> rules for first-order resolution apply
		 *  --> need to account for excepted points in the corresponding clause
		 */
		// propagate within EprClauses
		//TODO: possibly optimize (so not all clauses have to be treated)
		ArrayList<EprClause> toAdd = new ArrayList<>();
		for (EprClause otherEc : mEprClauses) {
			EprClause derivedClause = otherEc.setQuantifiedLiteral(eqlwe);
			if (derivedClause != null) { //TODO: derivedClause vs conflict clause distinction not nice..
				toAdd.add(derivedClause); //TODO: this would be cleaner if eprStateManager would manage all EprClauses
				
				if (derivedClause.isConflictClause()) {
					assert conflict == null : "what to do with several conflicts??"; //maybe one is enough (the state will change bc of backtracking anyway..)
					conflict = derivedClause;
					// TODO what if the conflict clause is not ground??
					// maybe just ground it with one constant? e.g. lambda?..
				}
			}
			updateFulFilledSets(otherEc);
		}
		mEprClauses.addAll(toAdd);
		
		// check if there is an Literal in the Engine that conflicts, or is unconstrained. In case propagate.
		for (EprGroundPredicateAtom engineAtom : eqlwe.mAtom.eprPredicate.getDPLLAtoms()) {
			Literal decideStatus = engineAtom.getDecideStatus();
			
			boolean polaritiesDifferOrUnconstrained = decideStatus == null || decideStatus.getSign() == 1 ^ eqlwe.mIsPositive;
			if (polaritiesDifferOrUnconstrained) {

				// is there a unifier?
				HashMap<TermVariable, Term> sub = engineAtom.getArgumentsAsTermTuple().match(eqlwe.mAtom.getArgumentsAsTermTuple());
				if (sub != null) {
					Literal propLit = eqlwe.mIsPositive ? engineAtom : engineAtom.negate();
					mGroundLiteralsToPropagate.add(propLit);
					mPropLitToExplanation.put(propLit, eqlwe.mExplanation.instantiateClause(null, sub));
				}
			}
		}

		return conflict;
	}

	@Override
	public Clause computeConflictClause() {
//		throw new UnsupportedOperationException();
		System.out.println("EPRDEBUG: computeConflictClause");
		for (Clause c : mNotFulfilledEprClauses) {
			EprClause eprClause = (EprClause)	c;
			
			// an epr clause looks like this:
			// x1 =/!= x2 \/ ... \/ xn+1 = c1 ... \/ (P1 ci/xi ... cj/xj) \/ ... \/ (non-EPR literals)
			// we have
			// - (dis)equalities over two quantified variables
			// - equalities over a quantified variable and a constant each
			// - predicates over quantified variables and/or constants
			// - non-epr literals (in mNotFulfilledEprClauses, they are all false (maybe unset??))
			Clause conflict = eprClause.check(mEprStateManager);
//			checkResult &= conflict == null;
			if (conflict != null)
				return conflict;
		}
		return null;
	}

	@Override
	public Literal getPropagatedLiteral() {
//		System.out.println("EPRDEBUG: getPropagatedLiteral");
		if (!mGroundLiteralsToPropagate.isEmpty()) {
			System.out.println("EPRDEBUG: getPropagatedLiteral propagating: " + mGroundLiteralsToPropagate.getFirst());
		}
		return mGroundLiteralsToPropagate.pollFirst();
	}

	@Override
	public Clause getUnitClause(Literal literal) {
//		System.out.println("EPRDEBUG: getUnitClause");
		Clause unitClause = mPropLitToExplanation.get(literal);
		System.out.println("EPRDEBUG: getUnitClause -- returning " + unitClause);
		assert unitClause != null;
		return unitClause;
	}

	@Override
	public Literal getSuggestion() {
		//TODO: think about how to get smart suggestions..
		System.out.println("EPRDEBUG: getSuggestion");
		return null;
	}

	@Override
	public void printStatistics(Logger logger) {
		System.out.println("EPRDEBUG: printStatistics");
	}

	@Override
	public void dumpModel(Logger logger) {
		System.out.println("EPRDEBUG: dumpmodel");
	}

	@Override
	public void increasedDecideLevel(int currentDecideLevel) {
		// TODO Auto-generated method stub
		System.out.println("EPRDEBUG: increasedDecideLevel");

	}

	@Override
	public void decreasedDecideLevel(int currentDecideLevel) {
		// TODO Auto-generated method stub
		System.out.println("EPRDEBUG: decreasedDecideLevel");

	}

	@Override
	public Clause backtrackComplete() {
		// TODO Auto-generated method stub
		System.out.println("EPRDEBUG: backtrackComplete");
		return null;
	}

	@Override
	public void restart(int iteration) {
		// TODO Auto-generated method stub
		System.out.println("EPRDEBUG: restart");

	}

	@Override
	public void removeAtom(DPLLAtom atom) {
		// TODO Auto-generated method stub
		System.out.println("EPRDEBUG: removeAtom" + atom);

	}

	@Override
	public Object push() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void pop(Object object, int targetlevel) {
		// TODO Auto-generated method stub

	}

	@Override
	public Object[] getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void fillInModel(Model model, Theory t, SharedTermEvaluator ste) {
		// TODO Auto-generated method stub

	}
	/**
	 * Given some literals where at least one variable is free (thus implicitly forall-quantified), 
	 * inserts the clause into the eprTheory,
	 * and returns the corresponding almost-all clause which is to be added in the DPLLEngine
	 * @param lits
	 * @param hook
	 * @param proof
	 * @return
	 */
	public void addEprClause(Literal[] lits, ClauseDeletionHook hook, ProofNode proof) {
		
		//TODO: do something about hook and proof..
		EprClause newEprClause = new EprClause(lits, mTheory, mEprStateManager);
		
		
		mEprClauses.add(newEprClause);
		mNotFulfilledEprClauses.add(newEprClause);
		
		for (Literal li : lits) {
			updateLiteralToClauses(li, newEprClause);
		}
		
//		newEprClause.updateClauseState(mEprStateManager);

//		// account for the current decide status of quantified literals
//		for (Literal qLit : mCurrentlySetQuantifiedLiterals) {
//			eprClause.setQuantifiedLiteral(qLit);
//			updateFulFilledSets(eprClause);
//		}
	}

	void updateLiteralToClauses(Literal lit, EprClause c) {
		HashSet<EprClause> clauses = mLiteralToClauses.get(lit);
		if (clauses == null) {
			clauses = new HashSet<EprClause>();
			mLiteralToClauses.put(lit, clauses);
		}
		clauses.add(c);
	}

	/**
	 * A term is an EPR atom, if it is
	 *  - an atom
	 *  - contains free Termvariables (i.e. implicitly quantified variables)
	 *  - an ApplicationTerm with function symbol either "=" or an uninterpreted predicate
	 *  further checks:
	 *  - may not contain function symbols
	 */
	public static boolean isQuantifiedEprAtom(Term idx) {
		if (idx.getFreeVars().length > 0) {
			if (idx instanceof ApplicationTerm) {
				if (isEprPredicate(((ApplicationTerm) idx).getFunction())) return true;
				if ((((ApplicationTerm) idx).getFunction()).getName().equals("=")) return true;
			}
		}
		return false;
	}

	private static boolean isEprPredicate(FunctionSymbol function) {
		//TODO: we should collect all the predicates that are managed by EPR --> implement a check accordingly, here
		if (function.getName().equals("not")) return false;
		if (function.getName().equals("or")) return false;
		return true;
	}
	
	public Set<Clause> getFulfilledClauses() {
		return mFulfilledEprClauses;
	}

	public Set<Clause> getNotFulfilledClauses() {
		return mNotFulfilledEprClauses;
	}

	public EprAtom getEprAtom(ApplicationTerm idx, int hash, int assertionStackLevel, Object mCollector) {
		if (idx.getFunction().getName().equals("=")) {
			assert idx.getFreeVars().length > 0;
		    ApplicationTerm subTerm = applyAlphaRenaming(idx, mCollector);
			return new EprEqualityAtom(subTerm, hash, assertionStackLevel);
		} else {
			EprPredicate pred = mFunctionSymbolToEprPredicate.get(idx.getFunction());
			if (pred == null) {
				pred = new EprPredicate(idx.getFunction(), idx.getParameters().length);
				mFunctionSymbolToEprPredicate.put(idx.getFunction(), pred);
				mEprStateManager.addNewEprPredicate(pred);
			}
			if (idx.getFreeVars().length == 0) {
				EprGroundPredicateAtom egpa = pred.getAtomForPoint(new TermTuple(idx.getParameters()));
				if (egpa == null) {
					egpa = new EprGroundPredicateAtom(idx, hash, assertionStackLevel, pred);
					pred.addDPLLAtom(egpa);
				}
				return egpa;
			} else {
				ApplicationTerm substitutedTerm = applyAlphaRenaming(idx, mCollector);
				return new EprQuantifiedPredicateAtom(substitutedTerm, hash, assertionStackLevel, pred);
			}
		}
	}

	private ApplicationTerm applyAlphaRenaming(ApplicationTerm idx, Object mCollector) {
		TermTuple tt = new TermTuple(idx.getParameters());

		HashMap<TermVariable, Term> sub;
		// mCollector is a BuildClause-Object 
		// --> we need to apply the same substitution in every literal of the clause..
		if (mCollector != null) {
			sub = mBuildClauseToAlphaRenamingSub.get(mCollector);
		} else {
			// if mCollector is null, this means we are in a unit clause (i think...), 
			// and we can just use a fresh substitution
			sub = new HashMap<>();
		}

		for (TermVariable fv : idx.getFreeVars()) {
			if (sub.containsKey(fv))
				continue;
			sub.put(fv, mTheory.createFreshTermVariable(fv.getName(), fv.getSort()));
		}
		TermTuple ttSub = tt.applySubstitution(sub);
		ApplicationTerm subTerm = mTheory.term(idx.getFunction(), ttSub.terms);
		return subTerm;
	}

	public void notifyAboutNewClause(Object buildClause) {
		mBuildClauseToAlphaRenamingSub.put(buildClause, new HashMap<TermVariable, Term>());
	}
}
