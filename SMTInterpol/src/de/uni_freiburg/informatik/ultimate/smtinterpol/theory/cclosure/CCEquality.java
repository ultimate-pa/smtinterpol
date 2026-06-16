/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleListable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class CCEquality extends DPLLAtom {
	private final CCTerm mLhs, mRhs;
	/**
	 * The constant offset of this equality: it states {@code mLhs == mRhs + mOffset}. For a plain equality this is
	 * {@link Rational#ZERO}; a non-zero value turns this into an offset equality, used to relate terms that differ by a
	 * constant (e.g. {@code a == b + 3}).
	 */
	private Rational mOffset = Rational.ZERO;
	CCEquality mDiseqReason;
	private LAEquality mLasd;
	private Rational mLAFactor;
	private final Entry mEntry;

	class Entry extends SimpleListable<Entry> {
		public CCEquality getCCEquality() {
			return CCEquality.this;
		}
	}

	CCEquality(final int assertionstacklevel, final CCTerm c1, final CCTerm c2) {
		super(HashUtils.hashJenkins(c1.hashCode(), c2), assertionstacklevel);
		mLhs = c1;
		mRhs = c2;
		mEntry = new Entry();
	}

	public CCTerm getLhs() {
		return mLhs;
	}

	public CCTerm getRhs() {
		return mRhs;
	}

	/**
	 * @return the constant offset of this equality, such that {@code getLhs() == getRhs() + getOffset()}.
	 */
	public Rational getOffset() {
		return mOffset;
	}

	public void setOffset(final Rational offset) {
		mOffset = offset;
	}

	public Entry getEntry() {
		return mEntry;
	}

	public LAEquality getLASharedData() {
		return mLasd;
	}

	public void setLASharedData(final LAEquality lasd, final Rational factor) {
		mLasd = lasd;
		mLAFactor = factor;
	}

	/**
	 * Returns the linar factor. This is the factor f, such that
	 * <code>f * (getLhs() - getRhs()) == getLASharedData().getVar()</code>
	 *
	 * @return the factor.
	 */
	public Rational getLAFactor() {
		return mLAFactor;
	}

	public void removeLASharedData() {
		mLasd = null;
		mLAFactor = null;
	}

	@Override
	public Term getSMTFormula(final Theory smtTheory) {
		final Term lhs = mLhs.getFlatTerm();
		final Term rhs = mRhs.getFlatTerm();
		if (mOffset.equals(Rational.ZERO)) {
			return smtTheory.term("=", lhs, rhs);
		}
		// this equality states lhs == rhs + mOffset
		return smtTheory.term("=", lhs, smtTheory.term("+", rhs, mOffset.toTerm(rhs.getSort())));
	}

	@Override
	public String toString() {
		if (mOffset.equals(Rational.ZERO)) {
			return mLhs + " == " + mRhs;
		}
		return mLhs + " == " + mRhs + " + " + mOffset;
	}
}
