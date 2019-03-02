/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;

public abstract class AbstractDawgLetter<LETTER> implements IDawgLetter<LETTER> {

	protected final Object mSortId;
	protected final DawgLetterFactory<LETTER> mDawgLetterFactory;

	public AbstractDawgLetter(final DawgLetterFactory<LETTER> dawgLetterFactory, final Object sortId) {
		assert sortId != null;
		mSortId = sortId;
		mDawgLetterFactory = dawgLetterFactory;
	}

	@Override
	public Object getSortId() {
		return mSortId;
	}


	@Override
	public final Set<IDawgLetter<LETTER>> difference(final IDawgLetter<LETTER> other) {
		final Set<IDawgLetter<LETTER>> result = new HashSet<IDawgLetter<LETTER>>();
		final Set<IDawgLetter<LETTER>> otherComplement = other.complement();
		// apply distributivity..
		for (final IDawgLetter<LETTER> oce : otherComplement) {
			final IDawgLetter<LETTER> intersectDl = this.intersect(oce);
			if (intersectDl instanceof EmptyDawgLetter<?>) {
				continue;
			}
			result.add(intersectDl);
		}
		assert !EprHelpers.hasEmptyLetter(result);
		return result;
	}
}
