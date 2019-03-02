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

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;


/**
 * Given a transition relation and an initial state, checks if the corresponding Dawg is
 *  - empty
 *  - universal
 *  - a singleton (i.e. accepts exactly one word)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class CheckEmptyUniversalSingleton<LETTER, COLNAMES> {


	private boolean mIsEmpty;
	private boolean mIsSingleton;
	private boolean mIsUniversal;

	private final DawgState mInitialState;
	private final DeterministicDawgTransitionRelation<DawgState, DawgLetter<LETTER>, DawgState> mTransitionRelation;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	private final DawgSignature<COLNAMES> mSignature;

	public CheckEmptyUniversalSingleton(final DawgFactory<LETTER, COLNAMES> dawgFactory,
			final DawgState initialState,
			final DeterministicDawgTransitionRelation<DawgState, DawgLetter<LETTER>, DawgState> transitionRelation,
			final DawgSignature<COLNAMES> signature) {
		mDawgFactory = dawgFactory;
		mInitialState =initialState;
		mTransitionRelation = transitionRelation;
		mSignature = signature;
		check();
	}

	private void check() {

		Set<DawgState> currentStates = new HashSet<DawgState>();
		currentStates.add(mInitialState);

		mIsUniversal = true;

		for (int i = 0; i < mSignature.getNoColumns(); i++) {
			final Set<DawgState> newCurrentStates = new HashSet<DawgState>();
			for (final DawgState cs : currentStates) {

				DawgLetter<LETTER> outLetters = null;
				for (final Pair<DawgLetter<LETTER>, DawgState> outEdge : mTransitionRelation.getOutEdgeSet(cs)) {

					if (outLetters == null) {
						outLetters = outEdge.getFirst();
					} else {
						outLetters = outLetters.union(outEdge.getFirst());
					}
					newCurrentStates.add(outEdge.getSecond());
				}
				mIsUniversal &= outLetters == null ? false : outLetters.isUniversal();

			}
			currentStates = newCurrentStates;
		}

		if (isUniversal()) {
			mIsEmpty = false;
			mIsSingleton = false;
			return;
		}

		/*
		 * emptiness and being singleton can be checked easily using the iterator.
		 *  EDIT (05.04.2017): maybe not so easy, because SimpleComplementDawgLetters, together with AllConstants may
		 *    lead to a Dawg that we want to consider non-empty (where the actual witnesses need more constants though),
		 *    but where the DawgIterator cannot give us a witness
		 */
		final DawgIterator<LETTER, COLNAMES> it =
				new DawgIterator<LETTER, COLNAMES>(mTransitionRelation, mInitialState, mSignature);
		if (!it.hasNextDawgPath()) {
			mIsEmpty = true;
			mIsSingleton = false;
			return;
		} else {
			mIsEmpty = false;
		}
		mIsSingleton = !it.hasNextDawgPath() && it.nextDawgPath().isSingletonDawgPath();

//		final DawgIterator<LETTER, COLNAMES> it =
//				new DawgIterator<LETTER, COLNAMES>(mTransitionRelation, mInitialState, mSignature);
//		if (!it.hasNext()) {
//			mIsEmpty = true;
//			mIsSingleton = false;
//			return;
//		} else {
//			mIsEmpty = false;
//		}
//		final List<LETTER> firstWord = it.next();
//		assert firstWord != null;
//		assert firstWord.size() == mSignature.getNoColumns();
//		if (it.hasNext()) {
//			mIsSingleton = false;
//		} else {
//			mIsSingleton = true;
//		}
	}

	public boolean isEmpty() {
		return mIsEmpty;
	}

	public boolean isSingleton() {
		return mIsSingleton;
	}

	public boolean isUniversal() {
		return mIsUniversal;
	}
}
