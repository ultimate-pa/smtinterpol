package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
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
	private ArrayList<EprClause> mClauses = new ArrayList<EprClause>();
	
//	ArrayList<EprPredicate> mEprPredicates = new ArrayList<EprPredicate>();
	
	/**
	 * Contains the DecideStackLiterals of the decide stack that have been derived taking into account
	 * all the clauses in this push state and the push states below and which have not been
	 * derived in any of the below push states.
	 */
	private Stack<DecideStackQuantifiedLiteral> mDecideStack = new Stack<DecideStackQuantifiedLiteral>();

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

	public List<EprClause> getClauses() {
		return mClauses;
	}

	public Iterator<EprClause> getClausesIterator() {
		return mClauses.iterator();
	}
	
	public Iterator<DecideStackQuantifiedLiteral> getDecideStackLiteralIterator() {
		return mDecideStack.iterator();
	}


	public void pushDecideStackLiteral(DecideStackQuantifiedLiteral decideStackQuantifiedLiteral) {
		mDecideStack.push(decideStackQuantifiedLiteral);
	}
	
	public void popDecideStackLiteral(DecideStackQuantifiedLiteral decideStackQuantifiedLiteral) {
		DecideStackQuantifiedLiteral top = mDecideStack.pop();
		assert top == decideStackQuantifiedLiteral : "TODO: not yet clear how this will work..";
	}
	
	public DecideStackLiteral peekDecideStack() {
		return mDecideStack.peek();
	}

	public DecideStackQuantifiedLiteral popDecideStack() {
		if (mDecideStack.isEmpty()) {
			return null;
		}
		return mDecideStack.pop();
	}
}
