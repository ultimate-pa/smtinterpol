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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
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
public class UniversalDawgLetter<LETTER, COLNAMES> extends AbstractDawgLetter<LETTER, COLNAMES> {

	UniversalDawgLetter(DawgLetterFactory<LETTER, COLNAMES> dlf, Object sortId) {
		super(dlf, sortId);
	}

	@Override
	public Set<IDawgLetter<LETTER, COLNAMES>> complement() {
//		return Collections.singleton(mDawgLetterFactory.getEmptyDawgLetter(mSortId));
		return Collections.emptySet();
	}

	@Override
	public IDawgLetter<LETTER, COLNAMES> intersect(IDawgLetter<LETTER, COLNAMES> other) {
		return other;
	}
	
//	@Override
//	public Set<IDawgLetter<LETTER, COLNAMES>> difference(IDawgLetter<LETTER, COLNAMES> other) {
//		return other.complement();
//	}
	
	@Override
	public boolean matches(LETTER ltr, List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		return true;
	}
	
	@Override
	public IDawgLetter<LETTER, COLNAMES> restrictToLetter(LETTER ltr) {
		return mDawgLetterFactory.getSingletonSetDawgLetter(ltr, mSortId);
	}

	@Override
	public Collection<LETTER> allLettersThatMatch(List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		return mDawgLetterFactory.getAllConstants(mSortId);
	}

	@Override
	public String toString() {
		return "UniversalDawgLetter";
	}
}