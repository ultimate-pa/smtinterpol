package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;

public class EprStateManager {
	
	private Stack<EprState> mEprStateStack = new Stack<EprState>();
	private Stack<Literal> mLiteralStack = new Stack<Literal>();
	
	private EprState baseState;
	
	
	HashMap<Set<Literal>, EprClause> mLiteralToClauses = new HashMap<>();
	public EqualityManager mEqualityManager;
	
//	private HashSet<EprClause> mAllClauses = new HashSet<>();

	public EprStateManager(EqualityManager eqMan) {
		baseState = new EprState();
		mEprStateStack.push(baseState);
		mEqualityManager =  eqMan;
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

	public Clause setGroundLiteral(Literal literal) {
		
		EprGroundPredicateAtom atom = (EprGroundPredicateAtom) literal.getAtom();
		
		// is there a conflict with one of the currently set quantified literals??
		for (EprState es : mEprStateStack) {
			for (EprQuantifiedLitWExcptns l : es.mSetLiterals) {
				if (l.mAtom.eprPredicate != atom.eprPredicate)
					continue;
				if (l.mIsPositive == (literal.getSign() == 1))
					continue; // polarities match --> no conflict
				TTSubstitution sub = l.mAtom.getArgumentsAsTermTuple().match(atom.getArgumentsAsTermTuple(), mEqualityManager);
				if (sub != null) {
					EprClause conflict =  l.mExplanation.instantiateClause(null, sub);
					return conflict;
				}
			}
		}
		// is there a conflict with one of the currently set points 
		// (taking into account the current equalities between constants)
		HashSet<TermTuple> possibleConflictPoints = this.getPoints(literal.getSign() != 1, atom.eprPredicate);
		for (TermTuple point : possibleConflictPoints) {
			TTSubstitution sub = point.match(atom.getArgumentsAsTermTuple(), mEqualityManager);
			if (sub != null) {
				// build conflict clause
				ArrayList<Literal> confLits = new ArrayList<>();

				confLits.add(literal.negate());

				EprGroundPredicateAtom atomOfPoint = atom.eprPredicate.getAtomForPoint(point);
				confLits.add(literal.getSign() != 1 ? atomOfPoint.negate() : atomOfPoint);

				for (int i = 0; i < point.arity; i++) {
					confLits.add(mEqualityManager.getCCEquality(
							(ApplicationTerm) point.terms[i],
							(ApplicationTerm)  atom.getArguments()[i]).negate());

				}
				
				Clause conflict = new Clause(confLits.toArray(new Literal[confLits.size()]));
				return conflict;
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
		System.out.println("EPRDEBUG (EprStateManager): setting Quantified literal: " + eqlwe);

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
	public boolean addDerivedClause(EprClause dc) {
//		System.out.println("EPRDEBUG (EprStateManager): adding derived clause " + dc);
//		mLiteralToClauses.put(dc.getLiteralSet(), dc);
		return mEprStateStack.peek().addDerivedClause(dc);
	}

	public boolean addBaseClause(EprClause bc) {
		System.out.println("EPRDEBUG (EprStateManager): adding base clause " + bc);
		return mEprStateStack.peek().addBaseClause(bc);
	}

	public ArrayList<EprClause> getTopLevelDerivedClauses() {
		return mEprStateStack.peek().getDerivedClauses();
	}

	public HashSet<EprClause> getAllClauses() {
		HashSet<EprClause> allClauses = new HashSet<>();
		for (EprState es : mEprStateStack) {
			allClauses.addAll(es.getBaseClauses());
			allClauses.addAll(es.getDerivedClauses());
		}
		return allClauses;
	}

	public HashSet<EprClause> getFulfilledClauses() {
		HashSet<EprClause> fulfilledClauses = new HashSet<>();
		for (EprClause ec : getAllClauses())
			if (ec.isFulfilled())
				fulfilledClauses.add(ec);
		return fulfilledClauses;
	}
	
	public HashSet<EprClause> getNotFulfilledClauses() {
		HashSet<EprClause> notFulfilledClauses = new HashSet<>();
		for (EprClause ec : getAllClauses())
			if (!ec.isFulfilled())
				notFulfilledClauses.add(ec);
		return notFulfilledClauses;
	}

	public HashSet<EprClause> getConflictClauses() {
		HashSet<EprClause> result = new HashSet<>();
		for (EprState es : mEprStateStack) {
			result.addAll(es.getConflictClauses());
		}
		return result;
	}
	/**
	 * makes sure that for the same set of literals only one clause is constructed.
	 * @param newLits
	 * @param theory
	 * @return
	 */
	public EprClause getClause(Set<Literal> newLits, Theory theory, Object explanation) {
		EprClause result = mLiteralToClauses.get(newLits);
		if (result == null) {
			result = new EprClause(newLits.toArray(new Literal[newLits.size()]), theory, this, explanation);
			System.out.println("EPRDEBUG (EprStateManager): creating new clause " + result);
			mLiteralToClauses.put(newLits, result);
		}
		return result;
	}

	/**
	 * Checks if the given literal is already set, or if something stronger is set.
	 * @param unifiedUnitLiteral
	 * @return
	 */
	public boolean isSubsumedInCurrentState(Literal lit) { //TODO possibly this needs to work on a QuantifiedLitWExcptns
		if (lit.getAtom().getDecideStatus() == lit) { // is it set in DPLL?
			return true;
		}
		if (!(lit.getAtom() instanceof EprPredicateAtom))
			return false;
		
		boolean isPositive = lit.getSign() == 1;
		EprPredicateAtom atom = (EprPredicateAtom) lit.getAtom();
			
		for (EprQuantifiedLitWExcptns sl : this.getSetLiterals()) {
			if (sl.mIsPositive != isPositive)
				continue;
			if (sl.mAtom.eprPredicate != atom.eprPredicate)
				continue;
			TermTuple slTT = sl.mAtom.getArgumentsAsTermTuple();
			TermTuple tt = atom.getArgumentsAsTermTuple();
			TTSubstitution sub = slTT.match(tt, mEqualityManager);
			if (slTT.isEqualOrMoreGeneralThan(tt))
				return true;
		}
		// TODO Auto-generated method stub
		return false;
	}
}
