package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

public class EprStateManager {
	
	private Stack<EprState> mEprStateStack = new Stack<EprState>();
	private Stack<Literal> mLiteralStack = new Stack<Literal>();
	
	private EprState baseState;

	public EprStateManager() {
		baseState = new EprState();
		mEprStateStack.push(baseState);
	}

	public void beginScope(Literal literal) {
		mLiteralStack.push(literal);
		mEprStateStack.push(new EprState());
	}

	/**
	 * Revert everything that followed from setting literal
	 *  - pop the corresponding EprState
	 *  - revert the fulfillability status of the remaining epr-clauses (in lower states)
	 * @param literal
	 */
	public void endScope(Literal literal) {
		mEprStateStack.pop();
		mLiteralStack.pop();
		
	}

	public boolean setPoint(boolean positive, EprGroundPredicateAtom atom) {
		return mEprStateStack.peek().setPoint(positive, atom);
	}
	
	public HashSet<TermTuple> getPoints(boolean positive, EprPredicate pred) {
		HashSet<TermTuple> result = new HashSet<>();
		for (EprState es : mEprStateStack) {
			if (positive)
				result.addAll(es.mPredicateToModel.get(pred).mPositivelySetPoints);
			else
				result.addAll(es.mPredicateToModel.get(pred).mNegativelySetPoints);
		}
		return result;
	}
	

}
