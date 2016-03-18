package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

public class EprStateManager {
	
	private Stack<EprState> mEprStateStack = new Stack<EprState>();
	private Stack<Literal> mLiteralStack = new Stack<Literal>();
	
	private EprState baseState;
	
	private HashSet<EprClause> mAllClauses = new HashSet<>();

	public EprStateManager() {
		baseState = new EprState();
		mEprStateStack.push(baseState);
	}

	public void beginScope(Literal literal) {
		mLiteralStack.push(literal);
		mEprStateStack.push(new EprState(mEprStateStack.peek()));
	}

	/**
	 * Revert everything that followed from setting literal
	 *  - pop the corresponding EprState
	 *  - revert the fulfillability status of the remaining epr-clauses (in lower states)
	 * @param literal
	 */
	public void endScope(Literal literal) {
		mEprStateStack.pop();
		Literal popped = mLiteralStack.pop();
		assert literal == popped;
		
	}

	public boolean setGroundLiteral(Literal literal) {
		return mEprStateStack.peek().setPoint(
				literal.getSign() == 1, 
				(EprGroundPredicateAtom) literal.getAtom());
	}
	
	public boolean setQuantifiedLiteralWithExceptions(EprQuantifiedLitWExcptns eqlwe) {
		return mEprStateStack.peek().setQuantifiedLiteralWithExceptions(eqlwe);
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

	public ArrayList<EprQuantifiedLitWExcptns> getSetLiterals() {
		ArrayList<EprQuantifiedLitWExcptns> result = new ArrayList<>();
		for (EprState es : mEprStateStack)
			result.addAll(es.mSetLiterals);
		return result;
	}

	public void addNewEprPredicate(EprPredicate pred) {
		 mEprStateStack.peek().addNewEprPredicate(pred);
		
	}

	public void addDerivedClause(EprClause dc) {
		mEprStateStack.peek().addDerivedClause(dc);
	}

	public ArrayList<EprClause> getTopLevelDerivedClauses() {
		return mEprStateStack.peek().getDerivedClauses();
	}
}
