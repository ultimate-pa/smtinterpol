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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgbuilders;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgStateFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.BinaryMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;

/**
 * This creates a new Dawg where some columns are existentially quantified. This means that
 * {@code evaluate(newdawg, word)} holds if and only if there is an extension of the word for the removed columns to
 * some word', such that {@code evaluate(olddawg, word)} holds.
 *
 * @author Jochen Hoenicke
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class ReorderDawgBuilder<LETTER, COLNAMES> extends DawgBuilder<LETTER> {
	private final DawgStateFactory<LETTER> mDawgStateFactory;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	private final Map<Pair<List<DawgLetter<LETTER>>, DawgState<LETTER, Boolean>>, DawgState<LETTER, Boolean>> mCache;
	private final Map<Set<DawgState<LETTER, Boolean>>, DawgState<LETTER, Boolean>> mUnionCache;

	public ReorderDawgBuilder(final DawgFactory<LETTER, COLNAMES> factory) {
		mDawgFactory = factory;
		mDawgStateFactory = mDawgFactory.getDawgStateFactory();
		mCache = new HashMap<>();
		mUnionCache = new HashMap<>();
	}

	private DawgLetter<LETTER> createUniversal(final DawgLetter<LETTER> template) {
		return mDawgFactory.getDawgLetterFactory().getUniversalDawgLetter(template.getSortId());
	}

	private DawgState<LETTER, Boolean> addLettersInFront(final List<DawgLetter<LETTER>> partialWord,
			DawgState<LETTER, Boolean> state) {
		DawgState<LETTER, Boolean> sink = mDawgFactory.createMapped(state, b -> false);
		for (int i = partialWord.size() - 1; i >= 0; i--) {
			final DawgLetter<LETTER> ltr = partialWord.get(i);
			final DawgLetter<LETTER> all = createUniversal(ltr);
			assert !ltr.isEmpty();
			if (ltr.isUniversal() || state == sink) {
				state = mDawgStateFactory.createIntermediateState(Collections.singletonMap(state, all));
			} else {
				state = mDawgStateFactory.createIntermediateState(new BinaryMap<>(state, ltr, sink, ltr.complement()));
			}
			sink = mDawgStateFactory.createIntermediateState(Collections.singletonMap(sink, all));
		}
		return state;
	}

	private DawgState<LETTER, Boolean> union(final Set<DawgState<LETTER, Boolean>> states) {
		DawgState<LETTER, Boolean> result = mUnionCache.get(states);
		if (result != null) {
			return result;
		}
		if (states.iterator().next().isFinal()) {
			for (final DawgState<LETTER, Boolean> component : states) {
				// If this is the true node or the only false node, return this component.
				result = component;
				if (component.getFinalValue()) {
					break;
				}
			}
		} else {
			// build the set of successors for each letter.
			Map<Set<DawgState<LETTER, Boolean>>, DawgLetter<LETTER>> newSuccessors = new HashMap<>();
			final Object sort = states.iterator().next().getTransitions().values().iterator().next().getSortId();
			newSuccessors.put(new HashSet<>(), mDawgFactory.getDawgLetterFactory().getUniversalDawgLetter(sort));
			for (final DawgState<LETTER, Boolean> component : states) {
				for (final Map.Entry<DawgState<LETTER, Boolean>, DawgLetter<LETTER>> entry : component.getTransitions()
						.entrySet()) {
					newSuccessors = merge(newSuccessors, entry.getKey(), entry.getValue());
				}
			}
			// build union recursively and build the transition to the union states.
			final Map<DawgState<LETTER, Boolean>, DawgLetter<LETTER>> newTrans = new HashMap<>();
			for (final Map.Entry<Set<DawgState<LETTER, Boolean>>, DawgLetter<LETTER>> entry : newSuccessors
					.entrySet()) {
				final DawgState<LETTER, Boolean> newDest = union(entry.getKey());
				addLetterToMap(newTrans, newDest, entry.getValue());
			}
			result = mDawgStateFactory.createIntermediateState(newTrans);
		}
		mUnionCache.put(states, result);
		return result;
	}

	private DawgState<LETTER, Boolean> internalReorder(final List<DawgLetter<LETTER>> partialWord, final int offset,
			final int[] newPositionForColumns, final DawgState<LETTER, Boolean> state, final int level) {

		Pair<List<DawgLetter<LETTER>>, DawgState<LETTER, Boolean>> cacheKey = new Pair<>(partialWord, state);
		DawgState<LETTER, Boolean> result = mCache.get(cacheKey);
		if (result != null) {
			return result;
		}

		if (level == newPositionForColumns.length) {
			result = addLettersInFront(partialWord, state);
		} else {
			final int newPosition = newPositionForColumns[level];
			assert newPosition >= offset;
			int firstNull = 0;
			while (partialWord.get(firstNull) != null) {
				firstNull++;
			}
			if (newPosition == offset + firstNull) {
				// This column is the first still unknown variable, which means we can just recurse with the remaining
				// columns. Remove the elements up to this column from partialWord.
				final List<DawgLetter<LETTER>> newPartialWord = partialWord.subList(firstNull + 1, partialWord.size());

				// Now recurse with the shorter list and build transition.
				final Map<DawgState<LETTER, Boolean>, DawgLetter<LETTER>> newTransition = new HashMap<>();
				for (final Map.Entry<DawgState<LETTER, Boolean>, DawgLetter<LETTER>> entry : state.getTransitions()
						.entrySet()) {
					final DawgState<LETTER, Boolean> newDest = internalReorder(newPartialWord, newPosition + 1,
							newPositionForColumns, entry.getKey(), level + 1);
					addLetterToMap(newTransition, newDest, entry.getValue());
				}
				result = mDawgStateFactory.createIntermediateState(newTransition);
				result = addLettersInFront(partialWord.subList(0, firstNull), result);
			} else {
				// This column needs more work.  We recurse with one more letter in partialWord set.
				// In the end we need to union the state.
				final Set<DawgState<LETTER, Boolean>> subsets = new HashSet<>();
				for (final Map.Entry<DawgState<LETTER, Boolean>, DawgLetter<LETTER>> entry : state.getTransitions()
						.entrySet()) {
					partialWord.set(newPosition - offset, entry.getValue());
					subsets.add(internalReorder(partialWord, offset, newPositionForColumns, entry.getKey(), level + 1));
				}
				// clean up partialWord
				partialWord.set(newPosition - offset, null);

				// Now union the subsets recursively.
				result = union(subsets);
			}
		}
		// make sure cacheKey is immutable by copying the partialWord.
		cacheKey = new Pair<>(new ArrayList<>(partialWord), state);
		mCache.put(cacheKey, result);
		return result;
	}

	public final DawgState<LETTER, Boolean> reorder(final DawgState<LETTER, Boolean> input,
			final List<DawgLetter<LETTER>> partialWord, final int[] newPositions) {
		return internalReorder(new ArrayList<>(partialWord), 0, newPositions, input, 0);
	}
}
