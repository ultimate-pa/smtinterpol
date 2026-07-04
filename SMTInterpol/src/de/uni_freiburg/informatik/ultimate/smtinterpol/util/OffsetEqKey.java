/*
 * Copyright (C) 2009-2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A lookup key identifying an (offset) equality by the affine fact it expresses:
 * the offset-free parts of its two sides (see {@link OffsetTerm}) together with
 * the constant offset {@code constant(lhs) - constant(rhs)} between them. Two
 * equalities with the same key denote the same fact {@code lhs = rhs}, which is
 * what lets a needed equality like {@code (= (+ x 5) (+ y 7))} be matched against
 * the clause literal {@code (= x (+ y 2))}. The two offset-free parts are kept
 * <em>separate</em> (rather than subtracted into one difference polynomial) so
 * that unrelated edges whose difference polynomials coincide up to sign — e.g.
 * {@code x+y = z+w+2} and {@code z-y = x-w-2} — do not collide.
 */
public final class OffsetEqKey {
	private final Term mLhs;
	private final Term mRhs;
	private final Rational mOffset;
	private final int mHash;

	public OffsetEqKey(final Term lhs, final Term rhs) {
		if (lhs.getSort().isNumericSort()) {
			final OffsetTerm lhsSplit = new OffsetTerm(lhs);
			final OffsetTerm rhsSplit = new OffsetTerm(rhs);
			mLhs = lhsSplit.getTerm();
			mRhs = rhsSplit.getTerm();
			mOffset = lhsSplit.getOffset().sub(rhsSplit.getOffset());
		} else {
			mLhs = lhs;
			mRhs = rhs;
			mOffset = Rational.ZERO;
		}
		final int lhsHash = mLhs.hashCode();
		final int rhsHash = mRhs.hashCode();
		if (lhsHash == rhsHash) {
			mHash = lhsHash * 31 + mOffset.abs().hashCode();
		} else if (lhsHash < rhsHash) {
			mHash = lhsHash * 37 + rhsHash * 31 + mOffset.hashCode();
		} else {
			mHash = rhsHash * 37 + lhsHash * 31 + mOffset.negate().hashCode();
		}
	}

	public Term getLhs() {
		return mLhs;
	}

	public Term getRhs() {
		return mRhs;
	}

	public Rational getOffset() {
		return mOffset;
	}

	@Override
	public int hashCode() {
		return mHash;
	}

	@Override
	public boolean equals(final Object other) {
		if (this == other) {
			return true;
		}
		if (!(other instanceof OffsetEqKey)) {
			return false;
		}
		final OffsetEqKey o = (OffsetEqKey) other;
		return (mOffset.equals(o.mOffset) && mLhs == o.mLhs && mRhs == o.mRhs)
				|| (mOffset.equals(o.mOffset.negate()) && mLhs == o.mRhs && mRhs == o.mLhs);
	}
}
