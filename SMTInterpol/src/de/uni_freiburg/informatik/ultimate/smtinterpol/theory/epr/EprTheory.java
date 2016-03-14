package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
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
	HashSet<Clause> mEprClauses = new HashSet<>();
	HashSet<Clause> mFulfilledEprClauses = new HashSet<>();
	HashSet<Clause> mNotFulfilledEprClauses = new HashSet<>();
	
	int mClauseCounter = 0;

//	ArrayList<EprClause> mEprUnitClauses = new ArrayList<>();
//	SimpleList<Clause> mFulfilledEprClauses = new SimpleList<>();
//	SimpleList<Clause> mNotFulfilledEprClauses = new SimpleList<>();
	
	HashMap<FunctionSymbol, EprPredicate> mEprPredicates = new HashMap<>();

	HashMap<Literal, HashSet<EprClause>> mLiteralToClauses = new HashMap<Literal, HashSet<EprClause>>();
	
	ArrayDeque<Literal> mGroundLiteralsToPropagate = new ArrayDeque<Literal>();

	private Theory mTheory;
	private DPLLEngine mEngine;

//	private Term mAlmostAllConstant;
//	
	public EprTheory(Theory th, DPLLEngine engine) {
		mTheory = th;
		mEngine = engine;
//		mAlmostAllConstant = th.term("@0");
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

		// does this literal occur in any of the EprClauses?
		// --> then check for satisfiability
		//   return a conflict clause in case
		//   possibly do (or cache) propagations
		// --> otherwise update the predicate model (held in the corresponding EprPredicate) accordingly

		DPLLAtom atom = literal.getAtom();
		
		if (atom instanceof EprPredicateAtom) {
			// literal is of the form (P c1 .. cn) (no quantification, but an EprPredicate)
			// it being set by the DPLLEngine (the quantified EprPredicateAtoms are not known to the DPLLEngine)
			assert atom.getSMTFormula(mTheory).getFreeVars().length == 0 : 
				"An atom that contains quantified variables should not be known to the DPLLEngine.";
			
			EprPredicate eprPred = ((EprPredicateAtom) atom).eprPredicate;

			boolean success = true;
			if (literal.getSign() == 1) 
				success &= eprPred.setPointPositive((EprPredicateAtom) atom);
			else 	
				success &= eprPred.setPointNegative((EprPredicateAtom) atom);
			assert success : "treat this case!";

			for (EprClause ec : mLiteralToClauses.get(literal)) {
				updateFulFilledSets(ec);
			}

			return null;
		} else if (atom instanceof EprEqualityAtom) {
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

		DPLLAtom atom = literal.getAtom();
		
		if (atom instanceof EprPredicateAtom) {
			// literal is of the form (P x1 .. xn)
			
			//update model
			EprPredicate eprPred = ((EprPredicateAtom) atom).eprPredicate;
			if (literal.getSign() == 1) eprPred.unSetPointPositive((EprPredicateAtom) atom);
			else 						eprPred.unSetPointNegative((EprPredicateAtom) atom);
			
			for (EprClause ec : mLiteralToClauses.get(literal)) {
				updateFulFilledSets(ec);
			}

			return;

		} else if (atom instanceof EprEqualityAtom) {
			assert false : "DPLLEngine is unsetting a quantified EprAtom --> this cannot be..";
			return;
		} else {
			// not an EprAtom 

			for (EprClause ec : mLiteralToClauses.get(literal)) {
				ec.unsetGroundLiteral(literal);
				updateFulFilledSets(ec);
			}

			System.out.println("EPRDEBUG: backtrackLiteral, new fulfilled clauses: " + mFulfilledEprClauses);
			System.out.println("EPRDEBUG: backtrackLiteral, new not fulfilled clauses: " + mNotFulfilledEprClauses);

			return;
		}
	}

//	/**
//	 * Changes the status of all EPR clauses from fulfilled to not fulfilled that contain
//	 * the given literal. (To be called by backtrackLiteral)
//	 * @param literal
//	 */
//	private void markEprClausesNotFulfilled(Literal literal) {
//		ArrayList<Clause> toRemove = new ArrayList<>();
//		for (Clause c : mFulfilledEprClauses) {
//			//check if this was the only literal that made the clause fulfilled
//			// if that is the case, mark it unfulfilled
//			if (c.contains(literal)) {
//				
//				boolean stillfulfilled = false;
//				for (int i = 0; i < c.getSize(); i++) {
//					Literal l  = c.getLiteral(i);
//					if (l == literal)
//						continue;
//					boolean isSet = l == l.getAtom().getDecideStatus();
//					stillfulfilled |= isSet;
//				}
//				if (!stillfulfilled) {
////						c.removeFromList();
////						mNotFulfilledEprClauses.append(c);
//					toRemove.add(c);
//					mNotFulfilledEprClauses.add(c);
//				}
//			}
//		}
//		mFulfilledEprClauses.removeAll(toRemove);
//	}

	@Override
	public Clause checkpoint() {
		System.out.println("EPRDEBUG: checkpoint");
		
		
		eprPropagate();
	
		
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
		
		return null;
	}

	/**
	 * Does/queues all propagations that can be made through unit clause ec
	 * @param ec a unit clause (i.e., unit in the current solver state)
	 */
	private void eprPropagate() {

		for (Clause c : mNotFulfilledEprClauses) {
			EprClause ec = (EprClause) c;
			if (ec.isUnitClause()) {
				Literal unitLiteral = ec.getUnitClauseLiteral();
				if (unitLiteral instanceof EprQuantifiedPredicateAtom) {
					/*
					 * propagate a quantified predicate
					 *  --> rules for first-order resolution apply
					 *  --> need to account for excepted points in the corresponding clause
					 */
					if (ec.mExceptedPoints.isEmpty()) {
						//TODO: possibly optimize (so not all clauses have to be treated)
						for (Clause otherClause : mEprClauses) {
							EprClause otherEc = (EprClause) otherClause;
							if (otherEc.equals(ec))
								continue;
							otherEc.setQuantifiedLiteral(unitLiteral);
							updateFulFilledSets(otherEc);
						}
					} else {
						throw new UnsupportedOperationException("todo: handle excepted points at first-order unit propagation");
					}
				} else {
					/*
					 * either an EprGroundAtom or a non EprAtom
					 * (plan atm: don't propagate EprEqualities)
					 * --> just propagate the literal through the normal means
					 */
					mGroundLiteralsToPropagate.add(unitLiteral);
				}
			}
		}
		
		
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
			Clause conflict = eprClause.check();
//			checkResult &= conflict == null;
			if (conflict != null)
				return conflict;
		}
		return null;
	}

	@Override
	public Literal getPropagatedLiteral() {
		System.out.println("EPRDEBUG: getPropagatedLiteral");
		return mGroundLiteralsToPropagate.pollFirst();
	}

	@Override
	public Clause getUnitClause(Literal literal) {
		// TODO Auto-generated method stub
//		return null;
//		throw new UnsupportedOperationException();
		System.out.println("EPRDEBUG: getUnitClause");
		return null;
	}

	@Override
	public Literal getSuggestion() {
		// TODO Auto-generated method stub
//		return null;
//		throw new UnsupportedOperationException();
		System.out.println("EPRDEBUG: getSuggestion");
		return null;
	}

	@Override
	public void printStatistics(Logger logger) {
		// TODO Auto-generated method stub
//		throw new UnsupportedOperationException();
		System.out.println("EPRDEBUG: printStatistics");
	}

	@Override
	public void dumpModel(Logger logger) {
		// TODO Auto-generated method stub
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
		EprClause eprClause = new EprClause(lits, mTheory, mClauseCounter++);
		mEprClauses.add(eprClause);
		mNotFulfilledEprClauses.add(eprClause);
		
		for (Literal li : lits) {
			updateLiteralToClauses(li, eprClause);
		}
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
	
//	public List<Clause> getFulfilledClauses() {
	public Set<Clause> getFulfilledClauses() {
		return mFulfilledEprClauses;
	}

//	public List<Clause> getNotFulfilledClauses() {
	public Set<Clause> getNotFulfilledClauses() {
		return mNotFulfilledEprClauses;
	}

	public EprAtom getEprAtom(ApplicationTerm idx, int hash, int assertionStackLevel) {
		if (idx.getFunction().getName().equals("=")) {
			return new EprEqualityAtom(idx, hash, assertionStackLevel);
		} else {
			EprPredicate pred = mEprPredicates.get(idx.getFunction());
			if (pred == null) {
				pred = new EprPredicate(idx.getFunction(), idx.getParameters().length);
				mEprPredicates.put(idx.getFunction(), pred);
			}
			if (idx.getFreeVars().length == 0) {
				return new EprGroundPredicateAtom(idx, hash, assertionStackLevel, pred);
			} else {
				return new EprQuantifiedPredicateAtom(idx, hash, assertionStackLevel, pred);
			}
		}
	}
}
