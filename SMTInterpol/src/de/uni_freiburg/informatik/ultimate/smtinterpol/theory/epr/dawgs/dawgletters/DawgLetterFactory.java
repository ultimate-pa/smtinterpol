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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheorySettings;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.NestedMap2;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class DawgLetterFactory<LETTER> {


	private final Map<Object, UniversalDawgLetter<LETTER>> mSortToUniversalDawgLetter =
			new HashMap<Object, UniversalDawgLetter<LETTER>>();
	private final Map<Object, EmptyDawgLetter<LETTER>> mSortToEmptyDawgLetter =
			new HashMap<Object, EmptyDawgLetter<LETTER>>();

	private final NestedMap2<Object, Set<LETTER>, SimpleDawgLetter<LETTER>> mSortToLettersToSimpleDawgLetter =
			new NestedMap2<Object, Set<LETTER>, SimpleDawgLetter<LETTER>>();
	private final NestedMap2<Object, Set<LETTER>, SimpleComplementDawgLetter<LETTER>> mSortToLettersToSimpleComplementDawgLetter =
			new NestedMap2<Object, Set<LETTER>, SimpleComplementDawgLetter<LETTER>>();

	private final DawgFactory<LETTER, ?> mDawgFactory;


	public DawgLetterFactory(final DawgFactory<LETTER, ?> dawgFactory) {
		mDawgFactory = dawgFactory;
	}

	public IDawgLetter<LETTER> getSingletonSetDawgLetter(final LETTER element, final Object sortId) {
		return getSimpleDawgLetter(Collections.singleton(element), sortId);
	}

	public UniversalDawgLetter<LETTER> getUniversalDawgLetter(final Object sortId) {
		UniversalDawgLetter<LETTER> result = mSortToUniversalDawgLetter.get(sortId);
		if (result == null) {
			result = new UniversalDawgLetter<LETTER>(this, sortId);
			mSortToUniversalDawgLetter.put(sortId, result);
		}
		return result;
	}

	public EmptyDawgLetter<LETTER> getEmptyDawgLetter(final Object sortId) {
		EmptyDawgLetter<LETTER> result = mSortToEmptyDawgLetter.get(sortId);
		if (result == null) {
			result = new EmptyDawgLetter<LETTER>(this, sortId);
			mSortToEmptyDawgLetter.put(sortId, result);
		}
		return result;
	}


	public Set<LETTER> getAllConstants(final Object sortId) {
		final Set<LETTER> result = mDawgFactory.getAllConstants(sortId);
		assert result != null;
		return result;
	}

	/**
	 * Takes a set of DawgLetters and returns a set of DawgLetters that represents the complement
	 * of the LETTERs represented by the input set.
	 *
	 * Conceptually a set of DawgLetters is a kind of DNF (a DawgLetter is a cube with one set-constraint
	 * and some equality and inequality constraints).
	 * This method has to negate the DNF and bring the result into DNF again.
	 * @param object
	 *
	 * @param outgoingDawgLetters
	 * @return
	 */
	public Set<IDawgLetter<LETTER>> complementDawgLetterSet(final Set<IDawgLetter<LETTER>> dawgLetters,
			final Object columnSort) {
		assert EprHelpers.dawgLettersHaveSameSort(dawgLetters);
		if (dawgLetters.isEmpty()) {
			return Collections.singleton((IDawgLetter<LETTER>) getUniversalDawgLetter(columnSort));
		}

		final Object sortId = ((AbstractDawgLetter<LETTER>) dawgLetters.iterator().next()).getSortId();

		Set<IDawgLetter<LETTER>> result = new HashSet<IDawgLetter<LETTER>>();
		result.add(getUniversalDawgLetter(sortId));

		for (final IDawgLetter<LETTER> currentDawgLetter : dawgLetters) {

			final Set<IDawgLetter<LETTER>> newResult = new HashSet<IDawgLetter<LETTER>>();

			/*
			 * for every dawgLetter d in the intermediate result and every constraint c in the current dawgLetter,
			 * 	add a new DawgLetter to the newResult
			 *   the new DawgLetter is the conjunction of the constraints in d with _not_ c.
			 */
			for (final IDawgLetter<LETTER> dawgLetterInIntermediateResult : result) {

				for (final IDawgLetter<LETTER> singleNegatedConstraintDlFromCurrentDl : currentDawgLetter
						.complement()) {
					newResult.add(dawgLetterInIntermediateResult.intersect(singleNegatedConstraintDlFromCurrentDl));
				}
			}
			result = newResult;
		}

		return result;
	}

	/**
	 *
	 * @param letters an implicitly disjunctive set of DawgLetters
	 * @return
	 */
	public boolean isUniversal(final Set<IDawgLetter<LETTER>> letters, final Object sortId) {
		if (letters.size() == 0) {
			return false;
		} else if (letters.size() == 1 && letters.iterator().next() instanceof EmptyDawgLetter<?>) {
			return false;
		} else if (letters.size() == 1 && letters.iterator().next() instanceof UniversalDawgLetter<?>) {
			return true;
		} else if (letters.size() >= 1 &&
				(letters.iterator().next() instanceof SimpleDawgLetter<?>
						|| letters.iterator().next() instanceof SimpleComplementDawgLetter<?>)) {
			/**
			 * the DawgLetters are universal (as a disjunction) if and only if the SimpleDawgLetters
			 * and the SimpleComplementDawgLetters complement each other perfectly.
			 */
			final Set<LETTER> unionNormal = new HashSet<LETTER>();
			final Set<LETTER> unionComplement = new HashSet<LETTER>();
			for (final IDawgLetter<LETTER> outLetter : letters) {
				if (outLetter instanceof SimpleDawgLetter<?>) {
					unionNormal.addAll(((SimpleDawgLetter<LETTER>) outLetter).getLetters());
				} else if (outLetter instanceof SimpleComplementDawgLetter<?>) {
					unionComplement.addAll(
							((SimpleComplementDawgLetter<LETTER>) outLetter).getComplementLetters());
				} else if (outLetter instanceof UniversalDawgLetter) {
					assert false : "a universal dawg letter and another one?";
				} else if (outLetter instanceof EmptyDawgLetter<?>) {
					// do nothing
				} else {
					assert false : "unexpected mixing of DawgLetter types";
				}
			}
			return unionNormal.equals(unionComplement);
		} else {
			final Set<IDawgLetter<LETTER>> complementSet = complementDawgLetterSet(letters, sortId);
			return  complementSet.isEmpty();
		}
//		assert false : "TODO";
//		return false;
	}

	public IDawgLetter<LETTER> getSimpleDawgLetter(final Set<LETTER> letters, final Object sortId) {
		if (letters.isEmpty()) {
			 return getEmptyDawgLetter(sortId);
		}

		IDawgLetter<LETTER> result = mSortToLettersToSimpleDawgLetter.get(sortId, letters);
		if (result == null) {
			result = new SimpleDawgLetter<LETTER>(this, letters, sortId);
			mSortToLettersToSimpleDawgLetter.put(sortId, letters, (SimpleDawgLetter<LETTER>) result);
		}
		return result;
	}

	public IDawgLetter<LETTER> getSimpleComplementDawgLetter(final Set<LETTER> letters, final Object sortId) {
		if (letters.isEmpty()) {
			 return getUniversalDawgLetter(sortId);
		}

		IDawgLetter<LETTER> result = mSortToLettersToSimpleComplementDawgLetter.get(sortId, letters);
		if (result == null) {
			result = new SimpleComplementDawgLetter<LETTER>(this, letters, sortId);
			mSortToLettersToSimpleComplementDawgLetter.put(sortId, letters,
					(SimpleComplementDawgLetter<LETTER>) result);
		}
		return result;
	}

	public boolean useSimpleDawgLetters() {
		return EprTheorySettings.UseSimpleDawgLetters;
	}
}
