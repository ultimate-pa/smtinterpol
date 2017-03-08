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

import java.util.Set;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

/**
 * The label of a transition in a (non-naive) Dawg.
 * Represents a set of LETTERs together with some (un)equals constraints regarding some COLNAMES.
 * Note that the different constraints are implicitly conjunctive.
 * Disjunctions are expressed via multiple edges.
 * 
 * @author Alexander Nutz
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class DawgLetterWithEqualities<LETTER, COLNAMES> extends AbstractSimpleDawgLetter<LETTER, COLNAMES> {
	
	private final Set<LETTER> mLetters;
	private final Set<COLNAMES> mEqualColnames;
	private final Set<COLNAMES> mUnequalColnames;
	
	final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;

	/**
	 * used only for the empty and universal DawgLetter right now.
	 * @param dlf
	 */
	DawgLetterWithEqualities(DawgLetterFactory<LETTER, COLNAMES> dlf, Object sortId) {
		super(sortId);
		mDawgLetterFactory = dlf;
		mLetters = null;
		mEqualColnames = null;
		mUnequalColnames = null;
	}
	
	public DawgLetterWithEqualities(Set<LETTER> newLetters, Set<COLNAMES> equalColnames, Set<COLNAMES> inequalColnames,
			DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory, Object sortId) {
		super(sortId);
		mDawgLetterFactory = dawgLetterFactory;
		mLetters = Collections.unmodifiableSet(newLetters);
		mEqualColnames = Collections.unmodifiableSet(equalColnames);
		mUnequalColnames = Collections.unmodifiableSet(inequalColnames);
		assert !mLetters.isEmpty() : "this letter is equivalent to the empty letter";
		assert equalsAndUnequalsDisjoint() : "equalities and inequalities contradict "
				+ "-- this should be replaced by the empty dawg letter";
	}

	private boolean equalsAndUnequalsDisjoint() {
		Set<COLNAMES> intersection = new HashSet<COLNAMES>(mEqualColnames);
		intersection.retainAll(mUnequalColnames);
		return intersection.isEmpty();
	}

	@Override
	public Set<IDawgLetter<LETTER, COLNAMES>> complement() {
		// TODO: get rid of AllConstants. Will need a symbolic complement representation..
		assert false : "TODO";

//		Set<LETTER> newLetters = new HashSet<LETTER>(mDawgLetterFactory.getAllConstants());
//		newLetters.removeAll(mLetters);
//	
//		Set<IDawgLetter<LETTER, COLNAMES>> result = new HashSet<IDawgLetter<LETTER,COLNAMES>>();
//		
//		for (COLNAMES cn : mEqualColnames) {
//			Set<COLNAMES> es = Collections.emptySet();
//			result.add(mDawgLetterFactory.getDawgLetter(
//					mDawgLetterFactory.getAllConstants(), es,  Collections.singleton(cn)));
//		}
//		for (COLNAMES cn : mUnequalColnames) {
//			Set<COLNAMES> es = Collections.emptySet();
//			result.add(mDawgLetterFactory.getDawgLetter(
//					mDawgLetterFactory.getAllConstants(), Collections.singleton(cn), es));
//		}	
//		return result;
		return null;
	}
	

	@Override
	public Set<IDawgLetter<LETTER, COLNAMES>> difference(IDawgLetter<LETTER, COLNAMES> other) {
		Set<IDawgLetter<LETTER, COLNAMES>> result = new HashSet<IDawgLetter<LETTER,COLNAMES>>();
		Set<IDawgLetter<LETTER, COLNAMES>> otherComplement = other.complement();
		for (IDawgLetter<LETTER, COLNAMES> oce : otherComplement) {
			result.add(this.intersect(oce));
		}
		return result;
	}

	@Override
	public IDawgLetter<LETTER, COLNAMES> intersect(IDawgLetter<LETTER, COLNAMES> other) {
		DawgLetterWithEqualities<LETTER, COLNAMES> otherDlwe = (DawgLetterWithEqualities<LETTER, COLNAMES>) other;
		Set<LETTER> mNewLetters = new HashSet<LETTER>(mLetters);
		Set<COLNAMES> mNewEqualColnames = new HashSet<COLNAMES>(mEqualColnames);
		Set<COLNAMES> mNewUnequalColnames = new HashSet<COLNAMES>(mUnequalColnames);
		
		mNewLetters.retainAll(otherDlwe.mLetters);
		mNewEqualColnames.addAll(otherDlwe.mEqualColnames);
		mNewUnequalColnames.addAll(otherDlwe.mUnequalColnames);
		
		return mDawgLetterFactory.getDawgLetter(mNewLetters, mEqualColnames, mUnequalColnames, mSortId);
	}

	@Override
	public boolean matches(LETTER ltr, List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		if (!mLetters.contains(ltr)) {
			return false;
		}
		for (COLNAMES cn : mEqualColnames) {
			Integer cnIndex = colnamesToIndex.get(cn);
			if (word.get(cnIndex) != ltr) {
				return false;
			}
		}
		for (COLNAMES cn : mUnequalColnames) {
			Integer cnIndex = colnamesToIndex.get(cn);
			if (word.get(cnIndex) == ltr) {
				return false;
			}
		}
		return true;
	}
	
	/**
	 * If this DawgLetter's mLetters-set contains ltr, return a DawgLetter with
	 *  mLetters = {ltr}, and the rest unchanged.
	 * Otherwise (ltr is not contained in mLetters), return null.
	 * 
	 * @param ltr
	 * @return
	 */
	public IDawgLetter<LETTER, COLNAMES> restrictToLetter(LETTER ltr) {
		if (!mLetters.contains(ltr)) {
			return mDawgLetterFactory.getEmptyDawgLetter(mSortId);
		}
		return mDawgLetterFactory.getDawgLetter(
				Collections.singleton(ltr), mEqualColnames, mUnequalColnames, mSortId);
	}

	public Set<LETTER> getLetters() {
		return mLetters;
	}

	public Set<COLNAMES> getEqualColnames() {
		return mEqualColnames;
	}

	public Set<COLNAMES> getUnequalColnames() {
		return mUnequalColnames;
	}

	@Override
	public Collection<LETTER> allLettersThatMatch(List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		// TODO Auto-generated method stub
		assert false : "TODO";
		return null;
	}

	@Override
	public String getSortId() {
		// TODO Auto-generated method stub
		assert false;
		return null;
	}
}

///**
// * A DawgLetter that captures no LETTER.
// * (probably this should not occur in any Dawg, but only as an intermediate result during construction
// *  -- an edge labelled with this letter should be omitted)
// * 
// * @author Alexander Nutz
// *
// * @param <LETTER>
// * @param <COLNAMES>
// */
//class EmptyDawgLetterWithEqualities<LETTER, COLNAMES> extends DawgLetterWithEqualities<LETTER, COLNAMES> {
//
//	EmptyDawgLetterWithEqualities(DawgLetterFactory<LETTER, COLNAMES> dlf, Object sortId) {
//		super(dlf, sortId);
//	}
//
//	@Override
//	public Set<IDawgLetter<LETTER, COLNAMES>> complement() {
//		return Collections.singleton(mDawgLetterFactory.getUniversalDawgLetter(mSortId));
//	}
//
//	@Override
//	public IDawgLetter<LETTER, COLNAMES> intersect(IDawgLetter<LETTER, COLNAMES> other) {
//		return this;
//	}
//
//	@Override
//	public Set<IDawgLetter<LETTER, COLNAMES>> difference(IDawgLetter<LETTER, COLNAMES> other) {
//		return Collections.singleton((IDawgLetter<LETTER, COLNAMES>) this);
//	}
//
//	@Override
//	public boolean matches(LETTER ltr, List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
//		return false;
//	}
//
//	@Override
//	public IDawgLetter<LETTER, COLNAMES> restrictToLetter(LETTER ltr) {
//		return null;
//	}
//}
//
///**
// * A DawgLetter that captures all LETTERs.
// * (i.e. the DawgLetter whose LETTER-set is "allConstants", and whose (un)equals-sets are empty)
// * 
// * @author Alexander Nutz
// *
// * @param <LETTER>
// * @param <COLNAMES>
// */
//class UniversalDawgLetterWithEqualities<LETTER, COLNAMES> extends  DawgLetterWithEqualities<LETTER, COLNAMES> {
//
//	UniversalDawgLetterWithEqualities(DawgLetterFactory<LETTER, COLNAMES> dlf, Object sortId) {
//		super(dlf, sortId);
//	}
//
//	@Override
//	public Set<IDawgLetter<LETTER, COLNAMES>> complement() {
//		return Collections.singleton(mDawgLetterFactory.getEmptyDawgLetter(mSortId));
//	}
//
//	@Override
//	public IDawgLetter<LETTER, COLNAMES> intersect(IDawgLetter<LETTER, COLNAMES> other) {
//		return other;
//	}
//	
//	@Override
//	public Set<IDawgLetter<LETTER, COLNAMES>> difference(IDawgLetter<LETTER, COLNAMES> other) {
//		return other.complement();
//	}
//	
//	@Override
//	public boolean matches(LETTER ltr, List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
//		return true;
//	}
//	
//	@Override
//	public IDawgLetter<LETTER, COLNAMES> restrictToLetter(LETTER ltr) {
//		return mDawgLetterFactory.getSingletonSetDawgLetter(ltr, mSortId);
//	}
//}