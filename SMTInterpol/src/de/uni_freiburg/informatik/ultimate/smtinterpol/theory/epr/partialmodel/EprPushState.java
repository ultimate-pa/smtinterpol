package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.ArrayList;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
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
	 * Contains the segment of the decidestack that is derivable when taking into account
	 * all the clauses in this push state and the push states below.
	 */
	Stack<DecideStackLiteral> mDecideStack = new Stack<DecideStackLiteral>();

	public void addClause(EprClause newClause) {
		mClauses.add(newClause);
	}

//	public void addEprPredicate(EprPredicate ep) {
//		mEprPredicates.add(ep);
//	}
	
}
