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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;

public class UniversalDawgLetterWithEqualities<LETTER, COLNAMES> extends AbstractDawgLetterWithEqualities<LETTER, COLNAMES> {
	
	public UniversalDawgLetterWithEqualities(DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory, 
			Set<COLNAMES> equalColnames, Set<COLNAMES> inequalColnames, Object sortId) {
		super(dawgLetterFactory, equalColnames, inequalColnames, sortId);
	}

	@Override
	public Set<IDawgLetter<LETTER, COLNAMES>> complement() {
		final Set<IDawgLetter<LETTER, COLNAMES>> result = new HashSet<IDawgLetter<LETTER,COLNAMES>>();
		
		// only needed because of java typing business..
		Set<COLNAMES> emptyColnames = Collections.emptySet();
		
		// (no set constraint needs to be added)
		
		// add the negated equality constraints
		for (COLNAMES eq : mEqualColnames) {
			result.add(mDawgLetterFactory.getUniversalDawgLetterWithEqualities(emptyColnames, 
					Collections.singleton(eq), mSortId));
		}

		// add the negated disequality constraints
		for (COLNAMES deq : mUnequalColnames) {
			result.add(mDawgLetterFactory.getUniversalDawgLetterWithEqualities(Collections.singleton(deq), 
					emptyColnames, mSortId));
		}

		return result;
	}

	@Override
	public IDawgLetter<LETTER, COLNAMES> intersect(IDawgLetter<LETTER, COLNAMES> other) {
		if (other instanceof UniversalDawgLetter<?, ?>) {
			return this;
		} else if (other instanceof EmptyDawgLetter<?, ?>) {
			return other;
		} 
		
		if (!(other instanceof AbstractDawgLetterWithEqualities<?, ?>)) {
			assert false : "?";
			return null;
		}
		
		/*
		 * compute new equality constraints
		 */
		final Set<COLNAMES> newEqualColnames = EprHelpers.computeUnionSet(mEqualColnames, 
				((AbstractDawgLetterWithEqualities<LETTER, COLNAMES>) other).mEqualColnames);
		final Set<COLNAMES> newUnequalColnames = EprHelpers.computeUnionSet(mUnequalColnames, 
				((AbstractDawgLetterWithEqualities<LETTER, COLNAMES>) other).mUnequalColnames);
		if (!EprHelpers.isIntersectionEmpty(newEqualColnames, newUnequalColnames)) {
			return mDawgLetterFactory.getEmptyDawgLetter(mSortId);
		}
		
		/*
		 * compute new set constraint
		 */
		if (other instanceof UniversalDawgLetterWithEqualities<?, ?>) {
			return mDawgLetterFactory.getUniversalDawgLetterWithEqualities(newEqualColnames, newUnequalColnames, mSortId);
		} else if (other instanceof DawgLetterWithEqualities<?, ?>) {
			final DawgLetterWithEqualities<LETTER, COLNAMES> otherDlwe = (DawgLetterWithEqualities<LETTER, COLNAMES>) other;
			return mDawgLetterFactory.getDawgLetterWithEqualities(otherDlwe.mLetters, 
					newEqualColnames, newUnequalColnames, mSortId);
		} else if (other instanceof ComplementDawgLetterWithEqualities<?, ?>) {
			final ComplementDawgLetterWithEqualities<LETTER, COLNAMES> otherDlwe = 
					(ComplementDawgLetterWithEqualities<LETTER, COLNAMES>) other;
			return mDawgLetterFactory.getComplementDawgLetterWithEqualities(
					otherDlwe.mComplementLetters, newEqualColnames, newUnequalColnames, mSortId);
		} else {
			assert false : "forgot a case?";
			return null;
		}
		
	}

//	@Override
//	public boolean matches(LETTER ltr, List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
//		// TODO Auto-generated method stub
//		return false;
//	}


	@Override
	public IDawgLetter<LETTER, COLNAMES> restrictToLetter(LETTER selectLetter) {
		return mDawgLetterFactory.getDawgLetterWithEqualities(
				Collections.singleton(selectLetter), mEqualColnames, mUnequalColnames, mSortId);
	}

	@Override
	public String toString() {
		return String.format("UniversalDawgLetterWE: %s", printedEqualityConstraints());
	}


}
