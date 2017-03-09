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

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;

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
public class DawgLetterWithEqualities<LETTER, COLNAMES> extends AbstractDawgLetterWithEqualities<LETTER, COLNAMES> {
	
	final Set<LETTER> mLetters;

	public DawgLetterWithEqualities(Set<LETTER> newLetters, Set<COLNAMES> equalColnames, Set<COLNAMES> inequalColnames,
			DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory, Object sortId) {
		super(dawgLetterFactory, inequalColnames, equalColnames, sortId);
		mLetters = Collections.unmodifiableSet(newLetters);
		assert !mLetters.isEmpty() : "this letter is equivalent to the empty letter";
		assert equalsAndUnequalsDisjoint() : "equalities and inequalities contradict "
				+ "-- this should be replaced by the empty dawg letter";
	}

	private boolean equalsAndUnequalsDisjoint() {
		Set<COLNAMES> intersection = new HashSet<COLNAMES>(mEqualColnames);
		intersection.retainAll(mUnequalColnames);
		return intersection.isEmpty();
	}

	/**
	 * This DawgLetter is a conjunction of the form (S /\ E1 /\ ... /\ U1 /\ ...)
	 *  where S is a set-constraint, Ei are equality constraints, Ui are disequality constrains
	 * The complement is a disjunction where each of the conjuncts is negated. 
	 * Disjunction is expressed through a set.
	 */
	@Override
	public Set<IDawgLetter<LETTER, COLNAMES>> complement() {
		final Set<IDawgLetter<LETTER, COLNAMES>> result = new HashSet<IDawgLetter<LETTER,COLNAMES>>();
		
		// only needed because of java typing business..
		Set<COLNAMES> emptyColnames = Collections.emptySet();

		// add the set-constraint not S
		result.add(mDawgLetterFactory.getComplementDawgLetterWithEqualities(mLetters, emptyColnames, emptyColnames, mSortId));
		
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
		final Set<LETTER> newLetters = new HashSet<LETTER>(mLetters);
		if (other instanceof UniversalDawgLetterWithEqualities<?, ?>) {
			// no further set constraints --> do nothing
		} else if (other instanceof DawgLetterWithEqualities<?, ?>) {
			final DawgLetterWithEqualities<LETTER, COLNAMES> otherDlwe = (DawgLetterWithEqualities<LETTER, COLNAMES>) other;
			newLetters.retainAll(otherDlwe.mLetters);
		} else if (other instanceof ComplementDawgLetterWithEqualities<?, ?>) {
			final ComplementDawgLetterWithEqualities<LETTER, COLNAMES> otherDlwe = 
					(ComplementDawgLetterWithEqualities<LETTER, COLNAMES>) other;
			newLetters.removeAll(otherDlwe.mComplementLetters);
		} else {
			assert false : "forgot a case?";
		}
		
		return mDawgLetterFactory.getDawgLetterWithEqualities(newLetters, newEqualColnames, newUnequalColnames, mSortId);
	}

	@Override
	public boolean matches(LETTER ltr, List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		if (!mLetters.contains(ltr)) {
			return false;
		}
		return super.matches(ltr, word, colnamesToIndex);
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
		return mDawgLetterFactory.getDawgLetterWithEqualities(
				Collections.singleton(ltr), mEqualColnames, mUnequalColnames, mSortId);
	}

	@Override
	public String toString() {
		return String.format("DawgLetter: %s, %s", mLetters, printedEqualityConstraints());
	}

}