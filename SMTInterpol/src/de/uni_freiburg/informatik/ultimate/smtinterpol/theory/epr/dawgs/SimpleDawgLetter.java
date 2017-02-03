/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class SimpleDawgLetter<LETTER, COLNAMES> implements IDawgLetter<LETTER, COLNAMES> {
	
	private final Set<LETTER> mLetters;
	private final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;
	
	public SimpleDawgLetter(DawgLetterFactory<LETTER, COLNAMES> dlf, Set<LETTER> letters) {
		mDawgLetterFactory = dlf;
		mLetters = letters;
	}

	@Override
	public Set<IDawgLetter<LETTER, COLNAMES>> complement() {
		final Set<LETTER> resultLetters = new HashSet<LETTER>();
		resultLetters.addAll(mDawgLetterFactory.getAllConstants());
		resultLetters.removeAll(mLetters);
		
		return Collections.singleton(mDawgLetterFactory.getSimpleDawgLetter(resultLetters));
	}

	@Override
	public Set<IDawgLetter<LETTER, COLNAMES>> difference(IDawgLetter<LETTER, COLNAMES> other) {
		SimpleDawgLetter<LETTER, COLNAMES> otherSdl = (SimpleDawgLetter<LETTER, COLNAMES>) other;
		final Set<LETTER> resultLetters = new HashSet<LETTER>();
		resultLetters.addAll(mLetters);
		resultLetters.removeAll(otherSdl.mLetters);
	
		return Collections.singleton(mDawgLetterFactory.getSimpleDawgLetter(resultLetters));
	}

	@Override
	public IDawgLetter<LETTER, COLNAMES> intersect(IDawgLetter<LETTER, COLNAMES> other) {
		SimpleDawgLetter<LETTER, COLNAMES> otherSdl = (SimpleDawgLetter<LETTER, COLNAMES>) other;
		final Set<LETTER> resultLetters = new HashSet<LETTER>();
		resultLetters.addAll(mLetters);
		resultLetters.retainAll(otherSdl.mLetters);
	
		return mDawgLetterFactory.getSimpleDawgLetter(resultLetters);
	}

	@Override
	public boolean matches(LETTER ltr, List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		return mLetters.contains(ltr);
	}

	public Set<LETTER> getLetters() {
		return mLetters;
	}

	@Override
	public IDawgLetter<LETTER, COLNAMES> restrictToLetter(LETTER selectLetter) {
		return mDawgLetterFactory.getSimpleDawgLetter(Collections.singleton(selectLetter));
	}

	@Override
	public Collection<LETTER> allLettersThatMatch(List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		return getLetters();
	}
	
	@Override
	public String toString() {
		return "SimpleDawgLetter: " + getLetters();
	}
}
