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

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;

public class ComplementDawgLetterWithEqualities<LETTER, COLNAMES> extends AbstractDawgLetterWithEqualities<LETTER, COLNAMES> {
	
	final Set<LETTER> mComplementLetters;

	public ComplementDawgLetterWithEqualities(Set<LETTER> complementLetters, 
			Set<COLNAMES> equalColnames, Set<COLNAMES> unequalColnames,
			DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory, Object sortId) {
		super(dawgLetterFactory, equalColnames, unequalColnames, sortId);
		assert !complementLetters.isEmpty() : "use UniversalDawgLetterWithEqualities instead!";
		mComplementLetters = complementLetters;
	}

	/**
	 * This DawgLetter is a conjunction of the form (not S /\ E1 /\ ... /\ U1 /\ ...)
	 *  where S is a set-constraint, Ei are equality constraints, Ui are disequality constraints
	 * The complement is a disjunction where each of the conjuncts is negated. 
	 * Disjunction is expressed through a set.
	 */
	@Override
	public Set<IDawgLetter<LETTER, COLNAMES>> complement() {
		final Set<IDawgLetter<LETTER, COLNAMES>> result = new HashSet<IDawgLetter<LETTER,COLNAMES>>();
		
		// only needed because of java typing business..
		Set<COLNAMES> emptyColnames = Collections.emptySet();

		// add the set-constraint S
		result.add(mDawgLetterFactory.getDawgLetterWithEqualities(mComplementLetters, emptyColnames, emptyColnames, mSortId));
		
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
			// no further set constraints --> do nothing
			return mDawgLetterFactory.getComplementDawgLetterWithEqualities(mComplementLetters, newEqualColnames, newUnequalColnames, mSortId);
		} else if (other instanceof DawgLetterWithEqualities<?, ?>) {
			// using the non-complement DawgLetter's intersect seems most elegant here..
			return other.intersect(this);
		} else if (other instanceof ComplementDawgLetterWithEqualities<?, ?>) {
			final Set<LETTER> newComplementLetters = new HashSet<LETTER>();
			final ComplementDawgLetterWithEqualities<LETTER, COLNAMES> otherDlwe = 
					(ComplementDawgLetterWithEqualities<LETTER, COLNAMES>) other;
			newComplementLetters.addAll(this.mComplementLetters);
			newComplementLetters.addAll(otherDlwe.mComplementLetters);

			return mDawgLetterFactory.getComplementDawgLetterWithEqualities(newComplementLetters, newEqualColnames, newUnequalColnames, mSortId);
		} else {
			assert false : "forgot a case?";
			return null;
		}
	}

	@Override
	public boolean matches(LETTER ltr, List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		if (mComplementLetters.contains(ltr)) {
			return false;
		}
		return super.matches(ltr, word, colnamesToIndex);
	}

	@Override
	public IDawgLetter<LETTER, COLNAMES> restrictToLetter(LETTER selectLetter) {
		if (mComplementLetters.contains(selectLetter)) {
			return mDawgLetterFactory.getEmptyDawgLetter(mSortId);
		}
		return mDawgLetterFactory.getDawgLetterWithEqualities(
				Collections.singleton(selectLetter), mEqualColnames, mUnequalColnames, mSortId);
	}

}
