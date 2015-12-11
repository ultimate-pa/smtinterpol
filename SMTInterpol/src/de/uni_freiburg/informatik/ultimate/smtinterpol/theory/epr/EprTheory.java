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
		
		System.out.println("EPRDEBUG: setLiteral" + literal);

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
			
			// update (non)fulfilled clauses (as it may make EprClauses true like any other, possibly non-epr, literal)


//			EprPredicate ePred = mEprPredicates.get(((EprPredicateAtom) atom).getPredicate());
//			if (literal.getSign() == 1) {
//				ePred.setPositive((EprAtom) literal.getAtom());
//			} else {
//				ePred.setNegative((EprAtom) literal.getAtom());
//			}

			return null;
//		} else if (atom instanceof NamedAtom) {
//			// literal is an auxilliary literal from the CNF transformation
//			// --> check if it occurs in one of the EPR-clauses
//			//      if it fulfills the clause "deactivate" it
//			//      otherwise "activate" it, possibly return a conflict clause?
//			// TODO: what does (de)activate mean?..
//			// FIXME: probably do the intricate stuff only at (check-sat)
//			return null;
			// meta-comment: NamedAtom is not a special case, any other non-epr-atom may occur
			// in an epr-clause as well and make that true or not..
		} else if (atom instanceof EprEqualityAtom) {
			//this should not happen because an EprEqualityAtom always has at least one
			// quantified variable, thus the DPLLEngine should not know about that atom
			assert false : "DPLLEngine is setting an EprAtom --> this cannot be..";
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
		// .. dual to setLiteral
		
		// TODO Auto-generated method stub

		System.out.println("EPRDEBUG: backtrackLiteral");
//		throw new UnsupportedOperationException();
	}

	@Override
	public Clause checkpoint() {
		// TODO Auto-generated method stub
		System.out.println("EPRDEBUG: checkpoint");
		return null;
//		throw new UnsupportedOperationException();
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
//		mEprClauses.append(new Clause(lits));
		mNotFulfilledEprClauses.append(new Clause(lits));
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


	public DPLLAtom getEprAtom(ApplicationTerm idx, int i, int j) {

		if (idx.getFunction().getName().equals("=")) {
			return new EprEqualityAtom(idx, i, j);
		} else {
			mEprPredicates.put(idx.getFunction(), new EprPredicate(idx.getFunction().getName()));
			return new EprPredicateAtom(idx, i, j, idx.getFunction());
		}
	}

}
