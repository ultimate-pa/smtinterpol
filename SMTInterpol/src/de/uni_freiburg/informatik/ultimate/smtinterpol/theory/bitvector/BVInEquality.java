package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;

public class BVInEquality extends DPLLAtom {
	public final static Annotation[] QUOTED_BV = new Annotation[] { new Annotation(":quotedBV", null) };
	private final Term mOriginalTerm;
	private final Theory mTheory;
	private final Term mLhs;
	private final Term mRhs;
	// enum type der relation
	public BVInEquality(final Term lhs, final Term rhs, final int assertionstacklevel) {
		super(lhs.getTheory().equals(lhs, rhs).hashCode(), assertionstacklevel);
		mTheory = lhs.getTheory();
		mLhs = lhs;
		mRhs = rhs;
		mOriginalTerm = mTheory.term("bvult", lhs, rhs);
	}

	@Override
	public Term getSMTFormula(final Theory smtTheory, final boolean quoted) {
		return quoted ? smtTheory.annotatedTerm(QUOTED_BV, mOriginalTerm) : mOriginalTerm;
	}

	// public boolean isSigned() {
	// if() {
	//
	// }
	// return false;
	// }

	public Term getRHS() {
		return mRhs;
	}

	public Term getLHS() {
		return mLhs;
	}
}

