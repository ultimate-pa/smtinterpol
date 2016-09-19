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
 * @author Alexander Nutz
 */
public class EprPushState {

	/**
	 * The clauses that came in through assert commands in the push-scope described by 
	 * this EprPushState
	 */
	private final ArrayList<EprClause> mClauses = new ArrayList<EprClause>();
	
	/**
	 * Contains the DecideStackLiterals of the decide stack that have been derived taking into account
	 * all the clauses in this push state and the push states below and which have not been
	 * derived in any of the below push states.
	 */
	private final Stack<DecideStackLiteral> mDecideStack = new Stack<DecideStackLiteral>();
	
	private final int mIndex;
	
	public EprPushState(int index) {
		mIndex = index;
	}

	public void addClause(EprClause newClause) {
		mClauses.add(newClause);
	}

	public List<EprClause> getClauses() {
		return mClauses;
	}

	public Iterator<EprClause> getClausesIterator() {
		return mClauses.iterator();
	}
	
	public Iterator<DecideStackLiteral> getDecideStackLiteralIterator() {
		return mDecideStack.iterator();
	}


	public void pushDecideStackLiteral(DecideStackLiteral decideStackQuantifiedLiteral) {
		mDecideStack.push(decideStackQuantifiedLiteral);
	}
	
	public DecideStackLiteral peekDecideStack() {
		return mDecideStack.peek();
	}

	public DecideStackLiteral popDecideStack() {
		if (mDecideStack.isEmpty()) {
			return null;
		}
		DecideStackLiteral dsl = mDecideStack.pop();
		dsl.unregister();
		assert dsl.getIndex().indexOnPushStatesDecideStack == mDecideStack.size() : "check dsl indices!";
		return dsl;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (DecideStackLiteral dsl : mDecideStack) {
			sb.append(dsl.toString());
		}
		return sb.toString();
	}
	
	public int getIndex() {
		return mIndex;
	}
	
	public int getDecideStackHeight() {
		return mDecideStack.size();
	}
}
