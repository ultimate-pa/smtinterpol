/*
 * Copyright (C) 2026 University of Freiburg
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

/**
 * A value of the form {@code getCCTerm() + getOffset()}: a CCTerm together with a constant offset. This is what every
 * consumer of a function application argument actually deals with once offset equalities exist (the argument of
 * {@code f(x+5)} is the CCTerm {@code x} plus the offset {@code 5}), as well as array indices, congruence arguments and
 * shared-term comparisons.
 *
 * <p>A bare {@link CCTerm} <em>is</em> a {@code CCParameter} with offset {@link Rational#ZERO}, so the common offset-free
 * case needs no wrapper object; only non-zero offsets allocate an {@link OffsettedCCTerm}. Use {@link #of} to build one
 * with this canonicalization.
 *
 * <p>The <em>value identity</em> of a parameter is the pair {@code (getRepresentative(), getOffsetToRep())}: two
 * parameters denote the same value iff they agree on both. Note this identity changes when the underlying class is
 * merged (the representative and its offset shift), so it must not be used as a key in a map that persists across
 * merges; see {@link #sameValueAs}.
 *
 * @author Jochen Hoenicke
 */
public interface CCParameter {

	/** The underlying CCTerm. */
	CCTerm getCCTerm();

	/** The constant offset added to the CCTerm; {@link Rational#ZERO} for a bare {@link CCTerm}. */
	Rational getOffset();

	/** The representative of the underlying CCTerm's congruence class. */
	default CCTerm getRepresentative() {
		return getCCTerm().getRepresentative();
	}

	/** The offset of this value relative to the representative: {@code value == value(representative) + this}. */
	default Rational getOffsetToRep() {
		return getCCTerm().getOffsetToRep().add(getOffset());
	}

	/** Whether this and the other parameter currently denote the same value (same representative and offset). */
	default boolean sameValueAs(final CCParameter other) {
		return getRepresentative() == other.getRepresentative() && getOffsetToRep().equals(other.getOffsetToRep());
	}

	/**
	 * Build a parameter for {@code term + offset}, returning the bare term when the offset is zero so that the common
	 * case allocates nothing.
	 */
	static CCParameter of(final CCTerm term, final Rational offset) {
		return offset.equals(Rational.ZERO) ? term : new OffsettedCCTerm(term, offset);
	}
}
