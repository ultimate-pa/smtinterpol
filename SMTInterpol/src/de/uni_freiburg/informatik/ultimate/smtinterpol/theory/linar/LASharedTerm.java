package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class LASharedTerm {
	private final Map<LinVar, Rational> mSummands;
	private final Rational mOffset;
	private final Term mSMTTerm;

	public LASharedTerm(final Term term, final Map<LinVar, Rational> summands, final Rational offset) {
		mSummands = summands;
		mSMTTerm = term;
		mOffset = offset;
	}

	public Map<LinVar, Rational> getSummands() {
		return mSummands;
	}

	public Rational getOffset() {
		return mOffset;
	}

	public Term getTerm() {
		return mSMTTerm;
	}

	@Override
	public String toString() {
		return mSMTTerm.toString();
	}
}
