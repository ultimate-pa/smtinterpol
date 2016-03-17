package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.HashSet;

public class EprPredicateModel {

	EprPredicate mEprPredicate;
	HashSet<TermTuple> mPositivelySetPoints = new HashSet<>();
	HashSet<TermTuple> mNegativelySetPoints = new HashSet<>();

	public EprPredicateModel(EprPredicate pred) {
		mEprPredicate = pred;
	}
	/**
	 * If the current model allows it, set the given point in the predicate model to "true", return true;
	 * If the point was already set to false, we have a conflict, do nothing, return false.
	 * @param atom
	 * @return
	 */
	public boolean setPointPositive(TermTuple point) {
		if (mNegativelySetPoints.contains(point)) {
			return false;
		} else {
			mPositivelySetPoints.add(point);
			return true;
		}
	}

	/**
	 * If the current model allows it, set the given point in the predicate model to "false", return true;
	 * If the point was already set to false, we have a conflict, do nothing, return false.
	 * @param point
	 * @return
	 */
	public boolean setPointNegative(TermTuple point) {
		if (mPositivelySetPoints.contains(point)) {
			return false;
		} else {
			mNegativelySetPoints.add(point);
			return true;
		}
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
}
