package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.ArrayList;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;

/**
 * Created by the stateManager for every push command in the smt script.
 * 
 * @author nutz
 */
public class EprPushState {

	/**
	 * The clauses that came in through assert commands in the push-scope described by 
	 * this EprPushState
	 */
	ArrayList<EprClause> mClauses = new ArrayList<EprClause>();
	
//	ArrayList<EprPredicate> mEprPredicates = new ArrayList<EprPredicate>();
	
	/**
	 * Contains the DecideStackLiterals of the decide stack that have been derived taking into account
	 * all the clauses in this push state and the push states below and which have not been
	 * derived in any of the below push states.
	 */
	Stack<DecideStackQuantifiedLiteral> mDecideStack = new Stack<DecideStackQuantifiedLiteral>();

	public void addClause(EprClause newClause) {
		mClauses.add(newClause);
	}

	public Clause setEprGroundLiteral() {
		// TODO Auto-generated method stub
		return null;
	}

	public void unsetEprGroundLiteral(Literal literal) {
		// TODO Auto-generated method stub
		
	}

	public void setEprClauseLiteral(ClauseLiteral lit) {
		
	}

	public void unsetEprClauseLiteral(ClauseLiteral lit) {
		
	}
//	public void addEprPredicate(EprPredicate ep) {
//		mEprPredicates.add(ep);
//	}
	
}
