package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
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
	SimpleList<Clause> mFulfilledEprClauses = new SimpleList<>();
	SimpleList<Clause> mNotFulfilledEprClauses = new SimpleList<>();
	
	HashMap<FunctionSymbol, EprPredicate> mEprPredicates = new HashMap<>();

	private Term mAlmostAllConstant;
	
	public EprTheory(Theory th) {
		mAlmostAllConstant = th.term("@0");
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
			// literal is of the form (P x1 .. xn)
			// it being set by the DPLLEngine means that it has been set because it 
			// occurs in a non-epr clause
			
			//update model
			EprPredicate eprPred = ((EprPredicateAtom) atom).getPredicate();
			boolean success;
			if (literal.getSign() == 1) success = eprPred.setPointPositive(new TermTuple(((EprPredicateAtom) atom).getArguments()));
			else 						success = eprPred.setPointNegative(new TermTuple(((EprPredicateAtom) atom).getArguments()));
			//return a unit clause saying that the point is already set negatively
			// question: can this occur at all?? when?
//			if (!success)
//				
			
			
			// 
			
			// update (non)fulfilled clauses (as it may make EprClauses true like any other, possibly non-epr, literal)
			for (Clause c : mNotFulfilledEprClauses) {
				if (c.contains(literal)) {
					c.removeFromList();
					mFulfilledEprClauses.append(c);
				}
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
			//          --> other theories will deal with it..?
			// (like standard DPLL)
			for (Clause c : mNotFulfilledEprClauses) {
				if (c.contains(literal)) {
					c.removeFromList();
					mFulfilledEprClauses.append(c);
				}
			}
			System.out.println("EPRDEBUG: setLiteral, new fulfilled clauses: " + mFulfilledEprClauses);
			System.out.println("EPRDEBUG: setLiteral, new not fulfilled clauses: " + mNotFulfilledEprClauses);

			return null;
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
			EprPredicate eprPred = ((EprPredicateAtom) atom).getPredicate();
			if (literal.getSign() == 1) eprPred.unSetPointPositive(new TermTuple(((EprPredicateAtom) atom).getArguments()));
			else 						eprPred.unSetPointNegative(new TermTuple(((EprPredicateAtom) atom).getArguments()));
			
			// update (non)fulfilled clauses
			for (Clause c : mFulfilledEprClauses) {
				//check if this was the only literal that made the clause fulfilled
				// if that is the case, mark it unfulfilled
				if (c.contains(literal)) {
					
					boolean stillfulfilled = false;
					for (int i = 0; i < c.getSize(); i++) {
						Literal l  = c.getLiteral(i);
						if (l == literal)
							continue;
						boolean isSet = l == l.getAtom().getDecideStatus();
						stillfulfilled |= isSet;
					}
					if (!stillfulfilled) {
						c.removeFromList();
						mNotFulfilledEprClauses.append(c);
					}
				}
			}
			return;
		} else if (atom instanceof EprEqualityAtom) {
			assert false : "DPLLEngine is unsetting a quantified EprAtom --> this cannot be..";
			return;
		} else {
			// not an EprAtom 
			for (Clause c : mFulfilledEprClauses) {
				//check if this was the only literal that made the clause fulfilled
				// if that is the case, mark it unfulfilled
				if (c.contains(literal)) {
					
					boolean stillfulfilled = false;
					for (int i = 0; i < c.getSize(); i++) {
						Literal l  = c.getLiteral(i);
						if (l == literal)
							continue;
						boolean isSet = l == l.getAtom().getDecideStatus();
						stillfulfilled |= isSet;
					}
					if (!stillfulfilled) {
						c.removeFromList();
						mNotFulfilledEprClauses.append(c);
					}
				}
			}

			System.out.println("EPRDEBUG: backtrackLiteral, new fulfilled clauses: " + mFulfilledEprClauses);
			System.out.println("EPRDEBUG: backtrackLiteral, new not fulfilled clauses: " + mNotFulfilledEprClauses);

			return;
		}
	}

	@Override
	public Clause checkpoint() {
		System.out.println("EPRDEBUG: checkpoint");
		
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
		
		for (Clause c : mNotFulfilledEprClauses) {
			EprClause e = (EprClause)	c;
			
			// an epr clause looks like this:
			// x1 =/!= x2 \/ ... \/ xn+1 = c1 ... \/ (P1 ci/xi ... cj/xj) \/ ... \/ (non-EPR literals)
			// we have
			// - (dis)equalities over two quantified variables
			// - equalities over a quantified variable and a constant each
			// - predicates over quantified variables and/or constants
			// - non-epr literals (in mNotFulfilledEprClauses, they are all false (maybe unset??))
			Clause conflict = e.check();
//			checkResult &= conflict == null;
			if (conflict != null)
				return conflict;
		}
		
		return null;
	}

	@Override
	public Clause computeConflictClause() {
		// TODO Auto-generated method stub
//		throw new UnsupportedOperationException();
		System.out.println("EPRDEBUG: computeConflictClause");
		return null;
	}

	@Override
	public Literal getPropagatedLiteral() {
		
		// unit propagation for EPR clauses ?
//		for (Clause c : mNotFulfilledEprClauses) {
//			
//		}
		
		// pure literal propagation for EPR clauses?

		System.out.println("EPRDEBUG: getPropagatedLiteral");
		return null;
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

	public void addClause(Literal[] lits, ClauseDeletionHook hook, ProofNode proof) {

		EprClause eprClause = new EprClause(lits);

		// Have the EprPredicates point to the clauses and literals they occur in.
		for (Literal l : lits) {
			if (l.getAtom() instanceof EprPredicateAtom
					&& ((EprPredicateAtom) l.getAtom()).isQuantified()) {
				EprPredicate pred = ((EprPredicateAtom) l.getAtom()).getPredicate();
				pred.addQuantifiedOccurence(l, eprClause);
			}
		}
		
		mNotFulfilledEprClauses.append(eprClause);
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
	
	public SimpleList<Clause> getFulfilledClauses() {
		return mFulfilledEprClauses;
	}

	public SimpleList<Clause> getNotFulfilledClauses() {
		return mNotFulfilledEprClauses;
	}


	public DPLLAtom getEprAtom(ApplicationTerm idx, int hash, int assertionStackLevel) {
		if (idx.getFunction().getName().equals("=")) {
			return new EprEqualityAtom(idx, hash, assertionStackLevel);
		} else {
			EprPredicate pred = mEprPredicates.get(idx.getFunction());
			if (pred == null) {
				pred = new EprPredicate(idx.getFunction());
				mEprPredicates.put(idx.getFunction(), pred);
			}
			return new EprPredicateAtom(idx, hash, assertionStackLevel, pred);
		}
	}

	
	public Term getAlmostAllConstant() {
		return mAlmostAllConstant;
	}
}
