package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;

public class EprTheory implements ITheory {

	@Override
	public Clause startCheck() {
		throw new UnsupportedOperationException();
		// TODO Auto-generated method stub
//		return null;
	}

	@Override
	public void endCheck() {
		// TODO Auto-generated method stub

		throw new UnsupportedOperationException();
	}

	@Override
	public Clause setLiteral(Literal literal) {
		// TODO Auto-generated method stub
		return null;
//		throw new UnsupportedOperationException();
	}

	@Override
	public void backtrackLiteral(Literal literal) {
		// TODO Auto-generated method stub

		throw new UnsupportedOperationException();
	}

	@Override
	public Clause checkpoint() {
		// TODO Auto-generated method stub
//		return null;
		throw new UnsupportedOperationException();
	}

	@Override
	public Clause computeConflictClause() {
		// TODO Auto-generated method stub
//		return null;
		throw new UnsupportedOperationException();
	}

	@Override
	public Literal getPropagatedLiteral() {
		// TODO Auto-generated method stub
		return null;
//		throw new UnsupportedOperationException();
	}

	@Override
	public Clause getUnitClause(Literal literal) {
		// TODO Auto-generated method stub
//		return null;
		throw new UnsupportedOperationException();
	}

	@Override
	public Literal getSuggestion() {
		// TODO Auto-generated method stub
//		return null;
		throw new UnsupportedOperationException();
	}

	@Override
	public void printStatistics(Logger logger) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public void dumpModel(Logger logger) {
		// TODO Auto-generated method stub

	}

	@Override
	public void increasedDecideLevel(int currentDecideLevel) {
		// TODO Auto-generated method stub

	}

	@Override
	public void decreasedDecideLevel(int currentDecideLevel) {
		// TODO Auto-generated method stub

	}

	@Override
	public Clause backtrackComplete() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void restart(int iteration) {
		// TODO Auto-generated method stub

	}

	@Override
	public void removeAtom(DPLLAtom atom) {
		// TODO Auto-generated method stub

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

	ArrayList<Literal[]> mClauses = new ArrayList<>();
	public void addClause(Literal[] lits, ClauseDeletionHook hook, ProofNode proof) {
		// TODO Auto-generated method stub
		mClauses.add(lits);
	}

	public static boolean isEprAtom(Term idx) {
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

}
