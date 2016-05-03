package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprQuantifiedUnitClause;

public class EprPredicateModel {

	EprPredicate mEprPredicate;
	HashSet<TermTuple> mPositivelySetPoints = new HashSet<>();
	HashSet<TermTuple> mNegativelySetPoints = new HashSet<>();
	HashSet<EprQuantifiedUnitClause> mPositivelySetQuantifiedLitsWE = new HashSet<>();
	HashSet<EprQuantifiedUnitClause> mNegativelySetQuantifiedLitsWE = new HashSet<>();

	public EprPredicateModel(EprPredicate pred) {
		mEprPredicate = pred;
	}
	
	public void setQuantifiedLitPositive(EprQuantifiedUnitClause eqlwe) {
		assert eqlwe.getPredicateLiteral().getSign() == 1;
		mPositivelySetQuantifiedLitsWE.add(eqlwe);
	}
	
	public void setQuantifiedLitNegative(EprQuantifiedUnitClause eqlwe) {
		assert eqlwe.getPredicateLiteral().getSign() != 1;
		mNegativelySetQuantifiedLitsWE.add(eqlwe);
	}

	
	public void unsetQuantifiedLitPositive(EprQuantifiedUnitClause eqlwe) {
		if (eqlwe.getPredicateLiteral().getSign() == 1)
			mPositivelySetQuantifiedLitsWE.remove(eqlwe);
		else
			mNegativelySetQuantifiedLitsWE.remove(eqlwe);
	}

	/**
	 * If the current model allows it, set the given point in the predicate model to "true", return true;
	 * If the point was already set to false, we have a conflict, do nothing, return false.
	 * UPDATE: do consistency check somewhere else 
	 *      (does not make much sense to check consistency wrt just one EprState in the stack)
	 * @param atom
	 * @return
	 */
	public void setPointPositive(TermTuple point) {
		assert !mNegativelySetPoints.contains(point);
		mPositivelySetPoints.add(point);
	}

	/**
	 * see "positive" variant
	 * @param point
	 * @return
	 */
	public void setPointNegative(TermTuple point) {
		assert !mPositivelySetPoints.contains(point);
		mNegativelySetPoints.add(point);
	}
	

	//the "unset"-methods should be made obsolete by the new EprState-management.. right?
//	public void unSetPointPositive(EprPredicateAtom atom) {
//        TermTuple point = new TermTuple(((EprPredicateAtom) atom).getArguments());
//		assert mPositivelySetPoints.contains(point) : "backtracking a point that was not set";
//		mPointToAtom.remove(point);
//		mPositivelySetPoints.remove(point);
//	}
//	
//	public void unSetPointNegative(EprPredicateAtom atom) {
//        TermTuple point = new TermTuple(((EprPredicateAtom) atom).getArguments());
//		assert mNegativelySetPoints.contains(point) : "backtracking a point that was not set";
//		mPointToAtom.remove(point);
//		mNegativelySetPoints.remove(point);
//	}
	
	@Override
	public String toString() {
		return "someEprPoints..";
	}
}
