package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;

public class BVEquality extends DPLLAtom {
	public final static Annotation[] QUOTED_BV = new Annotation[] { new Annotation(":quotedBV", null) };

	private final Term mLhs;
	private final Term mRhs;
	private final Term mOriginalTerm;

	public BVEquality(final Term lhs, final Term rhs, int assertionstacklevel) {
		super(lhs.getTheory().equals(lhs, rhs).hashCode(), assertionstacklevel);
		mOriginalTerm = lhs.getTheory().equals(lhs, rhs);
		mLhs = lhs;
		mRhs = rhs;
	}

	@Override
	public Term getSMTFormula(Theory smtTheory, boolean quoted) {
		return quoted ? smtTheory.annotatedTerm(QUOTED_BV, mOriginalTerm) : mOriginalTerm;
	}

	public Term getRHS() {
		return mRhs;
	}

	public Term getLHS() {
		return mLhs;
	}



}
