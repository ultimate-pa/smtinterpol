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
 * A DawgLetter that captures no LETTER.
 * (probably this should not occur in any Dawg, but only as an intermediate result during construction
 *  -- an edge labelled with this letter should be omitted)
 *
 * @author Alexander Nutz
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class EmptyDawgLetter<LETTER> extends AbstractDawgLetter<LETTER> {

	EmptyDawgLetter(final DawgLetterFactory<LETTER> dlf, final Object sortId) {
		super(dlf, sortId);
	}

	@Override
	public Set<IDawgLetter<LETTER>> complement() {
		return Collections.singleton((IDawgLetter<LETTER>) mDawgLetterFactory.getUniversalDawgLetter(mSortId));
	}

	@Override
	public IDawgLetter<LETTER> intersect(final IDawgLetter<LETTER> other) {
		return this;
	}

//	@Override
	// public Set<IDawgLetter<LETTER>> difference(IDawgLetter<LETTER> other) {
	//// return Collections.singleton((IDawgLetter<LETTER>) this);
	// return Collections.singleton((IDawgLetter<LETTER>) this);
//	}

	@Override
	public boolean matches(final LETTER ltr, final List<LETTER> word) {
		return false;
	}

	@Override
	public IDawgLetter<LETTER> restrictToLetter(final LETTER ltr) {
		assert false;
		return null;
	}

	@Override
	public Collection<LETTER> allLettersThatMatch(final List<LETTER> word) {
		return Collections.emptySet();
	}

	@Override
	public String toString() {
		return "EmptyDawgLetter";
	}

	@Override
	public IDawgLetter<LETTER> union(final IDawgLetter<LETTER> other) {
		return other;
	}
}

