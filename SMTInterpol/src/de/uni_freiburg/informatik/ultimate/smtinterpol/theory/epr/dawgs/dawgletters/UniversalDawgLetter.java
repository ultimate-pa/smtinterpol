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

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Set;

/**
 * A DawgLetter that captures all LETTERs.
 * (i.e. the DawgLetter whose LETTER-set is "allConstants", and whose (un)equals-sets are empty)
 *
 * @author Alexander Nutz
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class UniversalDawgLetter<LETTER> extends AbstractDawgLetter<LETTER> {

	UniversalDawgLetter(final DawgLetterFactory<LETTER> dlf, final Object sortId) {
		super(dlf, sortId);
	}

	@Override
	public Set<IDawgLetter<LETTER>> complement() {
		return Collections.emptySet();
	}

	@Override
	public IDawgLetter<LETTER> intersect(final IDawgLetter<LETTER> other) {
		return other;
	}

	@Override
	public boolean matches(final LETTER ltr, final List<LETTER> word) {
		return true;
	}

	@Override
	public IDawgLetter<LETTER> restrictToLetter(final LETTER ltr) {
		return mDawgLetterFactory.getSingletonSetDawgLetter(ltr, mSortId);
	}

	@Override
	public Collection<LETTER> allLettersThatMatch(final List<LETTER> word) {
		return mDawgLetterFactory.getAllConstants(mSortId);
	}

	@Override
	public String toString() {
		return "UniversalDawgLetter";
	}

	@Override
	public IDawgLetter<LETTER> union(final IDawgLetter<LETTER> other) {
		return this;
	}
}