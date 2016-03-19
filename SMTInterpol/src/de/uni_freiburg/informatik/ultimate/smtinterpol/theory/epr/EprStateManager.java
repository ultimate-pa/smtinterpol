package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
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

	public EprClause setGroundLiteral(Literal literal) {
		
		EprGroundPredicateAtom atom = (EprGroundPredicateAtom) literal.getAtom();
		
		// is there a conflict with one of the currently set quantified literals??
		for (EprState es : mEprStateStack) {
			for (EprQuantifiedLitWExcptns l : es.mSetLiterals) {
				if (l.mAtom.eprPredicate != atom.eprPredicate)
					continue;
				if (l.mIsPositive == (literal.getSign() == 1))
					continue; // polarities match --> no conflict
				HashMap<TermVariable, Term> sub = l.mAtom.getArgumentsAsTermTuple().match(atom.getArgumentsAsTermTuple());
				if (sub != null) {
					EprClause conflict =  l.mExplanation.instantiateClause(null, sub);
					return conflict;
				}
			}
		}
		
		
		// if there is no conflict set it..
		boolean success = mEprStateStack.peek().setPoint(
				literal.getSign() == 1, 
				(EprGroundPredicateAtom) literal.getAtom());
		assert success;
		return null;
	}
	
	public boolean setQuantifiedLiteralWithExceptions(EprQuantifiedLitWExcptns eqlwe) {
		
		//TODO: do a consistency check with
		// a) other quantified literals
		// b) the current ground literals
		
		return mEprStateStack.peek().setQuantifiedLiteralWithExceptions(eqlwe);
	}
	
	public HashSet<TermTuple> getPoints(boolean positive, EprPredicate pred) {
		//TODO: some caching here?
		HashSet<TermTuple> result = new HashSet<>();
		for (EprState es : mEprStateStack) {
			EprPredicateModel points = es.mPredicateToModel.get(pred);
			if (points == null) //maybe not all eprStates on the stack know the predicate
				continue;
			if (positive)
				result.addAll(points.mPositivelySetPoints);
			else
				result.addAll(points.mNegativelySetPoints);
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

	/**
	 * Adds a clause that is derivable in the current state.
	 * @param dc
	 */
	public void addDerivedClause(EprClause dc) {
		mEprStateStack.peek().addDerivedClause(dc);
	}

	public ArrayList<EprClause> getTopLevelDerivedClauses() {
		return mEprStateStack.peek().getDerivedClauses();
	}
}
