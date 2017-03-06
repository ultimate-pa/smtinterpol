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
public class SimpleDawgLetter<LETTER, COLNAMES> extends AbstractSimpleDawgLetter<LETTER, COLNAMES> {
	
	private final Set<LETTER> mLetters;
	private final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;
	
	public SimpleDawgLetter(DawgLetterFactory<LETTER, COLNAMES> dlf, Set<LETTER> letters, Object sortId) {
		super(sortId);
		assert letters.size() > 0 : "use EmptyDawgLetter instead";
		mDawgLetterFactory = dlf;
		mLetters = letters;
	}

	@Override
	public Set<IDawgLetter<LETTER, COLNAMES>> complement() {
		return Collections.singleton(mDawgLetterFactory.getSimpleComplementDawgLetter(mLetters, mSortId));
	}

	@Override
	public Set<IDawgLetter<LETTER, COLNAMES>> difference(IDawgLetter<LETTER, COLNAMES> other) {
		final Set<IDawgLetter<LETTER, COLNAMES>> otherComplement = other.complement();
		assert otherComplement.size() == 1 : "should be the case for simpleDawgLetters, right?";
		return Collections.singleton(this.intersect(otherComplement.iterator().next()));
	}

	@Override
	public IDawgLetter<LETTER, COLNAMES> intersect(IDawgLetter<LETTER, COLNAMES> other) {
		if (other instanceof UniversalDawgLetter<?, ?>) {
			return this;
		} else if (other instanceof EmptyDawgLetter<?, ?>) {
			return other;
		} else if (other instanceof SimpleDawgLetter<?, ?>) {
			final Set<LETTER> resultLetters = new HashSet<LETTER>(mLetters);
			resultLetters.retainAll(((SimpleDawgLetter<LETTER, COLNAMES>) other).getLetters());
			return mDawgLetterFactory.getSimpleDawgLetter(resultLetters, mSortId);
		} else if (other instanceof SimpleComplementDawgLetter<?, ?>) {
			final Set<LETTER> resultLetters = new HashSet<LETTER>(mLetters);
			resultLetters.removeAll(((SimpleComplementDawgLetter<LETTER, COLNAMES>) other).getComplementLetters());
			return mDawgLetterFactory.getSimpleDawgLetter(resultLetters, mSortId);
		} else {
			assert false : "not expected";
			return null;
		}	
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
		if (mLetters.contains(selectLetter)) {
			return mDawgLetterFactory.getSimpleDawgLetter(Collections.singleton(selectLetter), mSortId);
		} else {
			return mDawgLetterFactory.getEmptyDawgLetter(mSortId);
		}
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
