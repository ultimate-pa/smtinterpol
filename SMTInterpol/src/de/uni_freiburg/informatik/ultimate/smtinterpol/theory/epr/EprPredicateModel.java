package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.HashSet;

public class EprPredicateModel {

	EprPredicate mEprPredicate;
	HashSet<TermTuple> mPositivelySetPoints = new HashSet<>();
	HashSet<TermTuple> mNegativelySetPoints = new HashSet<>();
	HashSet<EprQuantifiedLitWExcptns> mPositivelySetQuantifiedLitsWE = new HashSet<>();
	HashSet<EprQuantifiedLitWExcptns> mNegativelySetQuantifiedLitsWE = new HashSet<>();

	public EprPredicateModel(EprPredicate pred) {
		mEprPredicate = pred;
	}
	
//	public boolean setTermTupleWithExceptionsPositive(TermTuple tt) {
//		assert tt.getFreeVars().size() > 0 : "for a point use the corresponding method!";
//		
//	}
	public void setQuantifiedLitPositive(EprQuantifiedLitWExcptns eqlwe) {
		assert eqlwe.mIsPositive;
		mPositivelySetQuantifiedLitsWE.add(eqlwe);
	}
	
	public void setQuantifiedLitNegative(EprQuantifiedLitWExcptns eqlwe) {
		assert !eqlwe.mIsPositive;
		mNegativelySetQuantifiedLitsWE.add(eqlwe);
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
