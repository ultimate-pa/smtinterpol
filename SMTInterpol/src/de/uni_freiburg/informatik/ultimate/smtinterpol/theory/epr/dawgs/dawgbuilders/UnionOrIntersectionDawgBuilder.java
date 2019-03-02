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

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.BinaryRelation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.Dawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DeterministicDawgTransitionRelation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetterFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgStateFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.PairDawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class UnionOrIntersectionDawgBuilder<LETTER, COLNAMES> {

	private DawgState mResultInitialState;
	private DeterministicDawgTransitionRelation<DawgState, DawgLetter<LETTER>, DawgState> mResultTransitionRelation;

	private final DawgStateFactory<LETTER, COLNAMES> mDawgStateFactory;
	private final Dawg<LETTER, COLNAMES> mFirstInputDawg;
	private final Dawg<LETTER, COLNAMES> mSecondInputDawg;
	private final DawgLetterFactory<LETTER> mDawgLetterFactory;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;

	public UnionOrIntersectionDawgBuilder(final Dawg<LETTER, COLNAMES> first, final Dawg<LETTER, COLNAMES> second,
			final DawgFactory<LETTER, COLNAMES> df) {
		assert first.getSignature().equals(second.getSignature()) : "signatures don't match!";
		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();

		mFirstInputDawg = first;
		mSecondInputDawg = second;

		mResultTransitionRelation =
				new DeterministicDawgTransitionRelation<DawgState, DawgLetter<LETTER>, DawgState>();

		mResultInitialState = mDawgStateFactory.getOrCreatePairDawgState(first.getInitialState(),
				second.getInitialState());

	}

	public Dawg<LETTER, COLNAMES> buildUnion() {
		return build(true);
	}

	public Dawg<LETTER, COLNAMES> buildIntersection() {
		return build(false);
	}

	/**
	 *
	 * @param doUnion if this flag is true, build a dawg that recognizes the union of mFirst and
	 *   mSecond, otherwise build a dawg that recognizes the intersection of the two
	 * @return
	 */
	private Dawg<LETTER, COLNAMES> build(final boolean doUnion) {
		Set<PairDawgState> currentStates = new HashSet<PairDawgState>();
		currentStates.add((PairDawgState) mResultInitialState);

		for (int i = 0; i < mFirstInputDawg.getColNames().size(); i++) {
			final Set<PairDawgState> nextStates = new HashSet<PairDawgState>();

			for (final PairDawgState cs : currentStates) {

				if (!cs.isFirstSink() && !cs.isSecondSink()) {

					final BinaryRelation<DawgLetter<LETTER>, DawgLetter<LETTER>> dividedDawgLetters =
							EprHelpers.divideDawgLetters(mDawgLetterFactory,
									cs.getFirst(),
									cs.getSecond(),
									mFirstInputDawg.getTransitionRelation(),
									mSecondInputDawg.getTransitionRelation());

					for (final DawgLetter<LETTER> origDl : dividedDawgLetters.getDomain()) {
						final DawgState firstTargetWithOrigDl = mFirstInputDawg.getTransitionRelation()
								.get(cs.getFirst(), origDl);
						final DawgState secondTargetWithOrigDl = mSecondInputDawg.getTransitionRelation()
								.get(cs.getSecond(), origDl);
						assert firstTargetWithOrigDl != null || secondTargetWithOrigDl != null;

						for (final DawgLetter<LETTER> dividedDl : dividedDawgLetters.getImage(origDl)) {
							final DawgState firstTargetWithDividedDl = getTargetForDividedDawgLetter(
									cs.getFirst(), mFirstInputDawg.getTransitionRelation(), dividedDl);
							final DawgState secondTargetWithDividedDl = getTargetForDividedDawgLetter(
									cs.getSecond(), mSecondInputDawg.getTransitionRelation(), dividedDl);

							if (firstTargetWithDividedDl != null && secondTargetWithDividedDl != null) {
								final PairDawgState newState = mDawgStateFactory.getOrCreatePairDawgState(
										firstTargetWithDividedDl, secondTargetWithDividedDl);
								if (mResultTransitionRelation.get(cs, dividedDl) != null) {
									assert mResultTransitionRelation.get(cs, dividedDl).equals(newState);
									continue;
								}
								nextStates.add(newState);
								mResultTransitionRelation.put(cs, dividedDl, newState);
							} else if (doUnion && firstTargetWithDividedDl == null
									&& secondTargetWithDividedDl != null) {
								final PairDawgState newState = mDawgStateFactory.getOrCreatePairDawgState(
										secondTargetWithDividedDl, true, false);
								if (mResultTransitionRelation.get(cs, dividedDl) != null) {
									assert mResultTransitionRelation.get(cs, dividedDl).equals(newState);
									continue;
								}

								nextStates.add(newState);
								mResultTransitionRelation.put(cs, dividedDl, newState);
							} else if (doUnion && firstTargetWithDividedDl != null
									&& secondTargetWithDividedDl == null) {
								final PairDawgState newState = mDawgStateFactory.getOrCreatePairDawgState(
										firstTargetWithDividedDl, false, true);
								if (mResultTransitionRelation.get(cs, dividedDl) != null) {
									assert mResultTransitionRelation.get(cs, dividedDl).equals(newState);
									continue;
								}

								nextStates.add(newState);
								mResultTransitionRelation.put(cs, dividedDl, newState);
							}
						}
					}
				} else if (doUnion && cs.isSecondSink()) {
					for (final Pair<DawgLetter<LETTER>, DawgState> firstOutEdge :
						mFirstInputDawg.getTransitionRelation().getOutEdgeSet(cs.getFirst())) {

						final PairDawgState ds = mDawgStateFactory.getOrCreatePairDawgState(firstOutEdge.getSecond(), false, true);
						nextStates.add(ds);
						mResultTransitionRelation.put(cs, firstOutEdge.getFirst(), ds);
						assert !EprHelpers.areStatesUnreachable(mResultTransitionRelation, mResultInitialState, nextStates);
						assert EprHelpers.isDeterministic(mResultTransitionRelation);
						assert !EprHelpers.hasDisconnectedTransitions(mResultTransitionRelation,
								mResultInitialState);
					}
				} else if (doUnion && cs.isFirstSink()) {
					for (final Pair<DawgLetter<LETTER>, DawgState> secondOutEdge :
						mSecondInputDawg.getTransitionRelation().getOutEdgeSet(cs.getSecond())) {
						final PairDawgState ds = mDawgStateFactory.getOrCreatePairDawgState(secondOutEdge.getSecond(), true, false);
						nextStates.add(ds);
						mResultTransitionRelation.put(cs, secondOutEdge.getFirst(), ds);
						assert !EprHelpers.areStatesUnreachable(mResultTransitionRelation, mResultInitialState, nextStates);
						assert EprHelpers.isDeterministic(mResultTransitionRelation);
						assert !EprHelpers.hasDisconnectedTransitions(mResultTransitionRelation,
								mResultInitialState);
					}
				}
			}
			currentStates = nextStates;
		}

		mResultTransitionRelation = EprHelpers.flattenDawgStates(mResultTransitionRelation);
		mResultInitialState = mResultInitialState.getFlatReplacement();

		return new Dawg<LETTER, COLNAMES>(mDawgFactory, mFirstInputDawg.getLogger(),
				 mFirstInputDawg.getColNames(), mResultTransitionRelation, mResultInitialState);
	}

	/**
	 * Computes the target state for the DawgLetter dividedDl given a source state and a transition relation.
	 *  Assumes that divideDl is either a subset of or disjoint from any outgoing dawgletter of the sourceState in
	 *  the transitionRelation.
	 * Returns null iff no outgoing edge from sourceState has an intersection with dividedDl.
	 *
	 * @param sourceState
	 * @param transitionRelation
	 * @param dividedDl
	 * @return
	 */
	private DawgState getTargetForDividedDawgLetter(
			final DawgState sourceState,
			final DeterministicDawgTransitionRelation<DawgState, DawgLetter<LETTER>, DawgState> transitionRelation,
			final DawgLetter<LETTER> dividedDl) {

		for (final Pair<DawgLetter<LETTER>, DawgState> outEdge : transitionRelation.getOutEdgeSet(sourceState)) {
			if (!(outEdge.getFirst().intersect(dividedDl).isEmpty())) {
				assert (!outEdge.getFirst().difference(dividedDl).isEmpty())
					|| outEdge.getFirst().equals(dividedDl): "assumption on dividedDl violated!?";
					return outEdge.getSecond();
			}
		}

		return null;
	}
}
