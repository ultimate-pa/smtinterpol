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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class SimpleComplementDawgLetter<LETTER, COLNAMES> extends AbstractDawgLetter<LETTER, COLNAMES> {
	
	/**
	 * the letters that are not matched by this DawgLetter
	 */
	final Set<LETTER> mComplementSet;
	

	public SimpleComplementDawgLetter(DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory,
			Set<LETTER> complementSet, Object sortId) {
		super(dawgLetterFactory, sortId);
		assert !complementSet.isEmpty();
		mComplementSet = complementSet;
	}

	@Override
	public Set<IDawgLetter<LETTER, COLNAMES>> complement() {
		return Collections.singleton(mDawgLetterFactory.getSimpleDawgLetter(mComplementSet, mSortId));
	}

//	@Override
//	public Set<IDawgLetter<LETTER, COLNAMES>> difference(IDawgLetter<LETTER, COLNAMES> other) {
//		final Set<IDawgLetter<LETTER, COLNAMES>> otherComplement = other.complement();
//		assert otherComplement.size() == 1 : "should be the case for simpleDawgLetters, right?";
//		final IDawgLetter<LETTER, COLNAMES> resultDl = this.intersect(otherComplement.iterator().next());
//		if (resultDl instanceof EmptyDawgLetter<?, ?>) {
//			return Collections.emptySet();
//		}
//		return Collections.singleton(resultDl);
//	}

	@Override
	public IDawgLetter<LETTER, COLNAMES> intersect(IDawgLetter<LETTER, COLNAMES> other) {
		assert other.getSortId().equals(this.getSortId());
		if (other instanceof UniversalDawgLetter<?, ?>) {
			return this;
		} else if (other instanceof EmptyDawgLetter<?, ?>) {
			return other;
		} else if (other instanceof SimpleDawgLetter<?, ?>) {
			/*
			 * return a letter that accepts all letters that are in other's (positive) set,
			 * and not in this's (complement) set
			 */
			final Set<LETTER> othersLetters = ((SimpleDawgLetter<LETTER, COLNAMES>) other).getLetters();
			final Set<LETTER> newSet = new HashSet<LETTER>(othersLetters);
			newSet.removeAll(mComplementSet);
			return mDawgLetterFactory.getSimpleDawgLetter(newSet, mSortId);
		} else if (other instanceof SimpleComplementDawgLetter<?, ?>) {
			/*
			 * return a DawgLetter that accepts all letters that are neither in this's
			 * set nor in the other's set
			 */
			final Set<LETTER> newComplement = new HashSet<LETTER>(mComplementSet);
			newComplement.addAll(((SimpleComplementDawgLetter<LETTER, COLNAMES>) other).getComplementLetters());
			return mDawgLetterFactory.getSimpleComplementDawgLetter(newComplement, mSortId);
		} else {
			assert false : "not expected";
			return null;
		}
	}

	@Override
	public boolean matches(LETTER ltr, List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		return !mComplementSet.contains(ltr);
	}

	@Override
	public Collection<LETTER> allLettersThatMatch(List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		Set<LETTER> result = new HashSet<LETTER>(mDawgLetterFactory.getAllConstants(mSortId));
		result.removeAll(mComplementSet);
		return result;
	}

	@Override
	public IDawgLetter<LETTER, COLNAMES> restrictToLetter(LETTER selectLetter) {
		if (mComplementSet.contains(selectLetter)) {
			return mDawgLetterFactory.getEmptyDawgLetter(mSortId);
		} else {
			return mDawgLetterFactory.getSingletonSetDawgLetter(selectLetter, mSortId);
		}
	}

	public Set<LETTER> getComplementLetters() {
		return mComplementSet;
	}
	
	@Override
	public String toString() {
		return "SimpleCompDL: " + mComplementSet;
	}

	@Override
	public IDawgLetter<LETTER, COLNAMES> union(IDawgLetter<LETTER, COLNAMES> other) {
		if (other instanceof EmptyDawgLetter<?, ?>) {
			return this;
		} else if (other instanceof UniversalDawgLetter<?, ?>) {
			return other;
		} else if (other instanceof SimpleDawgLetter<?, ?>) {
			final Set<LETTER> otherSet = ((SimpleDawgLetter<LETTER, COLNAMES>) other).getLetters();
			final HashSet<LETTER> newComplementSet = new HashSet<LETTER>(mComplementSet);
			newComplementSet.removeAll(otherSet);
			return mDawgLetterFactory.getSimpleComplementDawgLetter(newComplementSet, mSortId);
		} else if (other instanceof SimpleComplementDawgLetter<?, ?>) {
			// we take the intersection of the complementLetters
			final Set<LETTER> otherComplementSet = 
					((SimpleComplementDawgLetter<LETTER, COLNAMES>) other).getComplementLetters();
			final HashSet<LETTER> intersection = new HashSet<LETTER>(mComplementSet);
			intersection.retainAll(otherComplementSet);
			return mDawgLetterFactory.getSimpleComplementDawgLetter(intersection, mSortId);
		} else {
			assert false : "?";
			return null;
		}
	}

}
