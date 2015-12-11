package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class EprPredicateAtom extends EprAtom {

	private final EprPredicate mPredicate;
	private final int mArity;
	
	private HashSet<TermTuple> mPositivelySetPoints = new HashSet<>();
	private HashSet<TermTuple> mNegativelySetPoints = new HashSet<>();

	public EprPredicateAtom(ApplicationTerm term, int hash, int assertionstacklevel, EprPredicate pred) {
		super(term, hash, assertionstacklevel);
		mPredicate = pred;
		mArity = term.getParameters().length;
	}
	
	public EprPredicate getPredicate() {
		return mPredicate;
	}

	public Term[] getArguments() {
		return mTerm.getParameters();
	}
	
	public void setPointPositive(TermTuple point) {
		assert point.arity == mArity;
		assert !mNegativelySetPoints.contains(point) : "is that ok??";
		mPositivelySetPoints.add(point);
	}

	public void setPointNegative(TermTuple point) {
		assert point.arity == mArity;
		assert !mPositivelySetPoints.contains(point) : "is that ok??";
		mNegativelySetPoints.add(point);
	}
}
