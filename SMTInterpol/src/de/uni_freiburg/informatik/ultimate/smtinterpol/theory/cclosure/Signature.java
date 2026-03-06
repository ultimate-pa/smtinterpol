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

import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * A signature is a tuple of an opaque identifier and a non-empty array of CCTerms. It is used as the key for the
 * global signature-to-trigger map in CClosure. Hash and equality are based on the <em>representatives</em> of the
 * terms, so when representatives change (e.g. after a merge), the same term array yields a different signature key.
 *
 * @author Jochen Hoenicke, Jürgen Christ
 */
public final class Signature {

	private final Object mId;
	private final CCTerm[] mTerms;

	/**
	 * Create a signature with the given identifier and non-empty term array. The array may contain any CCTerms, not
	 * necessarily representatives. The array is copied defensively.
	 *
	 * @param id
	 *            opaque identifier (e.g. function symbol for congruence, or trigger id for reverse triggers).
	 * @param terms
	 *            non-empty array of CCTerms.
	 */
	public Signature(final Object id, final CCTerm[] terms) {
		if (terms == null || terms.length == 0) {
			throw new IllegalArgumentException("terms must be non-empty");
		}
		mId = id;
		mTerms = terms.clone();
	}

	public Object getId() {
		return mId;
	}

	/** Returns the number of terms in this signature. */
	public int getTermCount() {
		return mTerms.length;
	}

	/** Returns the term at the given index. */
	public CCTerm getTerm(final int index) {
		return mTerms[index];
	}

	/** Returns an unmodifiable list view of the terms. */
	public List<CCTerm> getTerms() {
		return Arrays.asList(mTerms);
	}

	@Override
	public int hashCode() {
		int h = mId.hashCode();
		for (final CCTerm t : mTerms) {
			h = HashUtils.hashJenkins(h, t.getRepresentative());
		}
		return h;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof Signature)) {
			return false;
		}
		final Signature other = (Signature) obj;
		if (!mId.equals(other.mId) || mTerms.length != other.mTerms.length) {
			return false;
		}
		for (int i = 0; i < mTerms.length; i++) {
			if (mTerms[i].getRepresentative() != other.mTerms[i].getRepresentative()) {
				return false;
			}
		}
		return true;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder("Sig[").append(mId);
		for (final CCTerm t : mTerms) {
			sb.append(',').append(t);
		}
		return sb.append(']').toString();
	}
}
