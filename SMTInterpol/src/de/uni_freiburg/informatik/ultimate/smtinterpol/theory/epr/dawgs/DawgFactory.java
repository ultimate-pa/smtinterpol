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

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.BinaryRelation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheorySettings;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetterFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgStateFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class DawgFactory<LETTER, COLNAMES> {

	// private final EprTheory mEprTheory;
	private final LogProxy mLogger;


	private final DawgLetterFactory<LETTER> mDawgLetterFactory;
	private final DawgStateFactory<LETTER, COLNAMES> mDawgStateFactory;

	/**
	 * Use naive Dawg implementation ("normal" one otherwise)
	 */
	private final boolean mUseNaiveDawgs = false;

	private final Map<SortedSet<COLNAMES>, IDawg<LETTER, COLNAMES>> mEmptyDawgs =
			new HashMap<SortedSet<COLNAMES>, IDawg<LETTER,COLNAMES>>();
	private final Map<SortedSet<COLNAMES>, IDawg<LETTER, COLNAMES>> mUniversalDawgs =
			new HashMap<SortedSet<COLNAMES>, IDawg<LETTER, COLNAMES>>();

	private final Map<Object, ScopedHashSet<LETTER>> mAllKnownConstants = new HashMap<Object, ScopedHashSet<LETTER>>();
	// private final ScopedHashMap<Object, Set<LETTER>> mAllKnownConstants = new ScopedHashMap<Object, Set<LETTER>>();
	// private final ScopedHashSet<String> mAllKnownSorts = new ScopedHashSet<String>();

	public DawgFactory(final EprTheory eprTheory) {
		// mEprStateManager = stateManager;
		mLogger = eprTheory.getLogger();

		if (mUseNaiveDawgs) {
			mDawgStateFactory = null;
			mDawgLetterFactory = null;
		} else {
			mDawgLetterFactory = new DawgLetterFactory<LETTER>(this);
			mDawgStateFactory = new DawgStateFactory<LETTER, COLNAMES>();
		}
	}

	private IDawg<LETTER, COLNAMES> createEmptyDawg(final SortedSet<COLNAMES> termVariables) {
		assert termVariables != null;

		if (mUseNaiveDawgs) {
			// TODO: when using naive dawgs we cannot cope with later changes to mAllConstants..
			// return new NaiveDawg<LETTER, COLNAMES>(termVariables, getAllConstants(), mLogger);
			// return new NaiveDawg<LETTER, COLNAMES>(termVariables, mAllKnownConstants, mLogger);
			assert false : "fix allConstants";
			return null;
		} else {
			return new Dawg<LETTER, COLNAMES>(this, mLogger, termVariables);
		}
	}

	/**
	 * Creates and returns a Dawg that accepts all words in Sigma^n.
	 * (where n = termVariables.length)
	 *
	 * @param termVariables
	 * @return
	 */
	private IDawg<LETTER, COLNAMES> createFullDawg(final SortedSet<COLNAMES> termVariables) {
		assert termVariables != null;
		if (mUseNaiveDawgs) {
			// return new NaiveDawg<LETTER, COLNAMES>(termVariables, getAllConstants(), mLogger).complement();
			// return new NaiveDawg<LETTER, COLNAMES>(termVariables, mAllKnownConstants, mLogger).complement();
			assert false : "fix allConstants";
			return null;
		} else {
			return new Dawg<LETTER, COLNAMES>(this, mLogger,
					termVariables, true);
		}
	}

	public IDawg<LETTER, COLNAMES> createOnePointDawg(
			final SortedSet<COLNAMES> sig, final List<LETTER> point) {
		if (mUseNaiveDawgs) {
			assert false : "fix allConstants";
			return null;
			// NaiveDawg<LETTER, COLNAMES> dawg =
			//// new NaiveDawg<LETTER, COLNAMES>(sig, getAllConstants(), mLogger);
			// new NaiveDawg<LETTER, COLNAMES>(sig, mAllKnownConstants, mLogger);
			// dawg.add(point);
			// return dawg;
		} else {
			return new Dawg<LETTER, COLNAMES>(this,
					mLogger, sig, point);
		}
	}

	public IDawg<LETTER, COLNAMES> copyDawg(final IDawg<LETTER, COLNAMES> dawg) {
		if (mUseNaiveDawgs) {
			final NaiveDawg<LETTER, COLNAMES> nd = (NaiveDawg<LETTER, COLNAMES>) dawg;
			return new NaiveDawg<LETTER, COLNAMES>(nd, mLogger);
		} else {
			if (dawg.isEmpty()) {
				// return new Dawg<LETTER, COLNAMES>(this, mLogger, mAllConstants, dawg.getColnames());
				// return createEmptyDawg(dawg.getColnames());
				return dawg;
			}
			if (dawg.isUniversal()) {
				// return new Dawg<LETTER, COLNAMES>(this, mLogger, mAllConstants, dawg.getColnames(), true);
				return dawg;
			}
			return new Dawg<LETTER, COLNAMES>(
					this,
					mLogger,
					dawg.getColNames(),
					new DeterministicDawgTransitionRelation<DawgState, DawgLetter<LETTER>, DawgState>(
							((Dawg<LETTER, COLNAMES>) dawg).getTransitionRelation()),
					((Dawg<LETTER, COLNAMES>) dawg).getInitialState());
		}
	}


	/**
	 * Used for translating from the signature of a DecideStackLiteral to the signature of an EprClause with respect to
	 * a clause literals signature.
	 * A DecideStackLiteral has one variable for each argument of the underlying predicate.
	 *
	 * example:
	 *  - some DSL says something like P(x_0 x_1 x_2 x_3)
	 *  - the overall clause signature may be (u v w x y z)
	 *  - the clause literals arguments may be (v a w v) (i.e. there may be constants, repetitions, and different orderings)
	 *
	 *  the input dawg has the signature of the DSL
	 *
	 *  then we want to change the columns of the input dawg such that they match the clause's signature
	 *  this entails
	 *  - renamings -- x_0 -> v, x_2 -> w
	 *  - if there are repetitions or constants, we have to select accordingly, in the example we only select points
	 *   where x_0 = x_3 and x_1 = a
	 *   --> from this we would get a dawg that describes the points wrt the clause literal
	 *  - we have to blow up the signature for the whole clause, i.e., for every missing column to the target signature we
	 *   insert a "X Sigma", i.e., we compute the cross product with the whole set of constants
	 *
	 *
	 * In short, and in the applications of the EprTheory, this translates a Dawg with the signature of an EprPredicate to a Dawg with the signature
	 * of a clause (according to the given translation mapping that is stored in each ClauseEprQuantifiedPredicate)
	 *
	 * @param dawg the dawg that is to be transformed
	 * @param translation a mapping from the variables in the input Dawgs signature to other TermVariables and/or constants
	 * @param targetSignature the target signature we want to blow up for in the end
	 * @return
	 */
	public IDawg<LETTER, COLNAMES> translatePredSigToClauseSig(
			final IDawg<LETTER, COLNAMES> dawg,
			final Map<COLNAMES, COLNAMES> translationCnToCn,
			final Map<COLNAMES, LETTER> translationCnToLtr,
			final SortedSet<COLNAMES> targetSignature) {

		final IDawg<LETTER, COLNAMES> result = dawg.translatePredSigToClauseSig(translationCnToCn,
				translationCnToLtr, new DawgSignature<COLNAMES>(targetSignature));
		assert result.getColNames().equals(targetSignature);
		return result;
	}



	/**
	 * From the input dawg and translation computes a dawg
	 *  - whose points are rearranged according to the new signature
	 *  - constants in the argList are filled in the corresponding places at every point
	 *  - we exploit that the order of arglist matches the sorting order of the newSignature
	 *    (that is fix for the given eprPredicate)
	 *  EDIT:
	 *   Pragmatically spoken this translated a dawg in the signature of an epr clause into a dawg in the signature of
	 *   a decide stack literal. For this it uses the information from one clause literal whose predicate matches the
	 *   decide stack literal's predicate.
	 * @param other
	 * @param binaryRelation a map translating the colnames of the old dawg ("other") to the colnames of the new dawg
	 *                    may not have a preimage for every new colname in the new signature because there constants
	 *                    from argList are filled in
	 *                     (could be computed from arglist, right?..)
	 * @param argList
	 * @param newSignature
	 * @return
	 */
	public IDawg<LETTER, COLNAMES> translateClauseSigToPredSig(
			final IDawg<LETTER, COLNAMES> other,
			final BinaryRelation<COLNAMES, COLNAMES> binaryRelation,
			final List<Object> argList,
			final SortedSet<COLNAMES> newSignature) {
		return other.translateClauseSigToPredSig(binaryRelation, argList, new DawgSignature<COLNAMES>(newSignature));
	}



	public LogProxy getLogger() {
		return mLogger;
	}

	// /////////////////////////////////////////////////////////////
	// ///////////////// test code /////////////////////////////////
	// /////////////////////////////////////////////////////////////
	// /**
	// * Some tests for the DawgFactory
	// * @param args
	// */
	// public static void main(String[] args) {
	//
	// // setup
	//
	// Set<Character> constants = new HashSet<Character>();
	// constants.add('a');
	// constants.add('b');
	// constants.add('c');
	//
	//
	// DawgFactory<Character, String> df =
	// new DawgFactory<Character, String>(constants, null);
	//
	// SortedSet<String> colNames1 = new TreeSet<String>();
	// colNames1.add("one");
	// colNames1.add("two");
	// // colNames1.add("three");
	// // colNames1.add("four");
	// // colNames1.add("five");
	//
	// SortedSet<String> colNames2 = new TreeSet<String>();
	// colNames2.add("alpha");
	// colNames2.add("beta");
	// colNames2.add("gamma");
	// // colNames1.add("delta");
	//
	//
	// IDawg<Character, String> d1 = df.createFullDawg(colNames1);
	//
	// System.out.println("d1: (one, two), Sigma^*");
	// System.out.println(d1);
	//
	// IDawg<Character, String> d2 = df.createEmptyDawg(colNames2);
	// List<Character> word1 = new ArrayList<Character>();
	// word1.add('a');
	// word1.add('a');
	// word1.add('b');
	// d2 = d2.add(word1);
	//
	// List<Character> word2 = new ArrayList<Character>();
	// word2.add('a');
	// word2.add('b');
	// word2.add('b');
	// d2 = d2.add(word2);
	//
	// System.out.println("d2: (alpha, beta, gamma), { aab, abb } ");
	// System.out.println(d2);
	//
	// // tests for renameSelectAndProject
	//
	//// Map<String, Object> translation3 = new HashMap<String, Object>();
	//// translation3.put("alpha", "bla");
	//// translation3.put("beta", "bla");
	//// translation3.put("gamma", "blub");
	////
	//// IDawg<Character, String> d3 = df.translatePredSigToClauseSig(d2, translation3, d2.getColnames());
	////
	//// System.out.println("d3: rnsP(d2, {alpha -> bla, beta -> bla, gamma -> blub)");
	//// System.out.println("expecting: (bla, blub) {ab}");
	//// System.out.println(d3);
	////
	//// Map<String, Object> translation4 = new HashMap<String, Object>();
	//// translation4.put("alpha", "bla");
	//// translation4.put("beta", "bla");
	//// translation4.put("gamma", 'a');
	////
	//// IDawg<Character, String> d4 = df.translatePredSigToClauseSig(d2, translation4, d2.getColnames());
	////
	//// System.out.println("d4: rnsP(d2, {alpha -> bla, beta -> bla, gamma -> 'a')");
	//// System.out.println("expecting: (bla) {}");
	//// System.out.println(d4);
	////
	//// Map<String, Object> translation5 = new HashMap<String, Object>();
	//// translation5.put("alpha", "bla");
	//// translation5.put("beta", "bla");
	//// translation5.put("gamma", 'b');
	////
	//// IDawg<Character, String> d5 = df.translatePredSigToClauseSig(d2, translation5, d2.getColnames());
	//
	//// System.out.println("d5: rnsP(d2, {alpha -> bla, beta -> bla, gamma -> 'b')");
	//// System.out.println("expecting: (bla) {a}");
	//// System.out.println(d5);
	//
	// // tests for renameAndRestoreConstants
	//
	//// BinaryRelation<String, String> translation6 = new BinaryRelation<String, String>();
	//// translation6.addPair("alpha", "cinque");
	//// translation6.addPair("beta", "uno");
	//// translation6.addPair("gamma", "quattro");
	//
	// Map<String, String> translation6 = new HashMap<String, String>();
	// translation6.put("cique", "alpha");
	// translation6.put("uno", "beta");
	// translation6.put("quattro", "gamma");
	//
	// List<Object> argList1 = new ArrayList<Object>();
	// argList1.add("beta");
	// argList1.add('B');
	// argList1.add("gamma");
	// argList1.add('A');
	// argList1.add("alpha");
	//
	// SortedSet<String> newSignature1 = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
	// newSignature1.add("uno");
	// newSignature1.add("due");
	// newSignature1.add("tre");
	// newSignature1.add("quattro");
	// newSignature1.add("cinque");
	//
	//
	// IDawg<Character, String> d6 = df.translateClauseSigToPredSig(d2, translation6, argList1, newSignature1);
	//
	// System.out.println("d6: rnRc(d2, {alpha -> uno, beta -> due, gamma -> tre), "
	// + "(beta, B, gamma, A, alpha)" + newSignature1);
	// System.out.println("expecting: (due, cinque, quattro, tre, uno) {aBbAa, aBbAb}");
	// System.out.println(d6);
	//
	// }

	public DawgLetterFactory<LETTER> getDawgLetterFactory() {
		return mDawgLetterFactory;
	}

	public DawgStateFactory<LETTER, COLNAMES> getDawgStateFactory() {
		return mDawgStateFactory;
	}

	public IDawg<LETTER, COLNAMES> getEmptyDawg(final SortedSet<COLNAMES> signature) {
		IDawg<LETTER, COLNAMES> result = mEmptyDawgs.get(signature);
		if (result == null) {
			result = createEmptyDawg(signature);
			mEmptyDawgs.put(signature, result);
		}
		return result;
	}

	public IDawg<LETTER, COLNAMES> getUniversalDawg(final SortedSet<COLNAMES> signature) {
		IDawg<LETTER, COLNAMES> result = mUniversalDawgs.get(signature);
		if (result == null) {
			result = createFullDawg(signature);
			mUniversalDawgs.put(signature, result);
		}
		return result;
	}

	// @Deprecated
	// public ScopedHashMap<String, Set<LETTER>> getAllConstants() {
	// return mAllKnownConstants;
	// }

	public Set<LETTER> getAllConstants(final Object sortId) {
		final Set<LETTER> result = mAllKnownConstants.get(sortId);
		// assert result != null;
		return result;
	}

	public void push() {
		for (final Entry<Object, ScopedHashSet<LETTER>> en : mAllKnownConstants.entrySet()) {
			en.getValue().beginScope();
		}
		// mAllKnownConstants.beginScope();
		// mAllKnownSorts.beginScope();
	}

	public void pop() {
		for (final Entry<Object, ScopedHashSet<LETTER>> en : mAllKnownConstants.entrySet()) {
			en.getValue().endScope();
		}
		// mAllKnownConstants.endScope();
		// mAllKnownSorts.endScope();
	}

	public void addConstant(final Object sortId, final LETTER constant) {
		// mAllKnownConstants.addAll(constants);
		// Set<LETTER> set = mAllKnownConstants.get(sortId);
		ScopedHashSet<LETTER> set = mAllKnownConstants.get(sortId);
		if (set == null) {
			// set = new HashSet<LETTER>();
			set = new ScopedHashSet<LETTER>();
			mAllKnownConstants.put(sortId, set);
		}
		set.add(constant);
	}

	public Dawg<LETTER, COLNAMES> closeDawgUnderSymmetryAndTransitivity(final Dawg<LETTER, COLNAMES> inputDawg) {

		final UnionFind<LETTER> unionFind = new UnionFind<LETTER>();

		LETTER universalPartitionRepresentative = null;

		Object sort = null;

		/*
		 * go through each connected pair of edges in the dawg. Join their partitions.
		 */
		for (final Pair<DawgLetter<LETTER>, DawgState> outEdge1 :
		inputDawg.getTransitionRelation().getOutEdgeSet(inputDawg.getInitialState())) {
			final DawgState outEdge1Target = outEdge1.getSecond();
			final DawgLetter<LETTER> outEdge1DL = outEdge1.getFirst();

			// final boolean dl1IsUniversal = outEdge1DL instanceof UniversalDawgLetter<?, ?>
			// || outEdge1DL instanceof SimpleComplementDawgLetter<?, ?>;

			assert !(outEdge1DL.isEmpty());

			if (outEdge1DL.isUniversal()) {
				return (Dawg<LETTER, COLNAMES>) getUniversalDawg(inputDawg.getColNames());
			}

			sort = outEdge1DL.getSortId();

			/*
			 * announce letters to unionFind
			 */
			for (final LETTER letter : outEdge1DL.getRawLetters()) {
				unionFind.findAndConstructEquivalenceClassIfNeeded(letter);
			}

			for (final Pair<DawgLetter<LETTER>, DawgState> outEdge2 :
			inputDawg.getTransitionRelation().getOutEdgeSet(outEdge1Target)) {
				final DawgState outEdge2Target = outEdge2.getSecond();
				final DawgLetter<LETTER> outEdge2DL = outEdge2.getFirst();

				assert !(outEdge2DL.isEmpty());

				if (outEdge2DL.isUniversal()) {
					return (Dawg<LETTER, COLNAMES>) getUniversalDawg(inputDawg.getColNames());
				}

				/*
				 * announce letters to unionFind
				 */
				for (final LETTER letter : outEdge2DL.getRawLetters()) {
					unionFind.findAndConstructEquivalenceClassIfNeeded(letter);
				}

				// final boolean dl2IsUniversal = outEdge2DL instanceof UniversalDawgLetter<?, ?>
				// || outEdge2DL instanceof SimpleComplementDawgLetter<?, ?>;

				if (!outEdge1DL.isComplemented() && !outEdge2DL.isComplemented()) {
					for (final LETTER l1 : outEdge1DL.getLetters()) {
						for (final LETTER l2 : outEdge2DL.getLetters()) {
							unionFind.union(l1, l2);
						}
					}
				} else if (!outEdge1DL.isComplemented() && outEdge2DL.isComplemented()) {
					for (final LETTER l1 : outEdge1DL.getLetters()) {
						for (final LETTER l2 : unionFind.getAllRepresentatives()) {
							if (outEdge2DL.matches(l2)) {
								unionFind.union(l1, l2);
								universalPartitionRepresentative = unionFind.find(l1);
							}
						}
					}
				} else if (outEdge1DL.isComplemented() && !outEdge2DL.isComplemented()) {
					for (final LETTER l1 : outEdge2DL.getLetters()) {
						for (final LETTER l2 : unionFind.getAllRepresentatives()) {
							if (outEdge1DL.matches(l2)) {
								unionFind.union(l1, l2);
								universalPartitionRepresentative = unionFind.find(l1);
							}
						}
					}
				} else {
					assert outEdge1DL.isComplemented() && outEdge2DL.isComplemented();
					for (final LETTER l1 : unionFind.getAllRepresentatives()) {
						for (final LETTER l2 : unionFind.getAllRepresentatives()) {
							if (outEdge1DL.matches(l1) && outEdge2DL.matches(l2)) {
								unionFind.union(l1, l2);
								universalPartitionRepresentative = unionFind.find(l1);
							}
						}
					}
				}
			}
		}


		final DeterministicDawgTransitionRelation<DawgState, DawgLetter<LETTER>, DawgState> transitionRelation =
				new DeterministicDawgTransitionRelation<DawgState, DawgLetter<LETTER>, DawgState>();

		final DawgState initialState = mDawgStateFactory.createDawgState();
		final DawgState finalState = mDawgStateFactory.createDawgState();

		final Set<LETTER> lettersNotInUniversalPartition = new HashSet<LETTER>();

		/*
		 * make transitions for all except the universal partition
		 */
		for (final Set<LETTER> eqClass : unionFind.getAllEquivalenceClasses()) {
			final boolean isUniversal =
					unionFind.find(eqClass.iterator().next()).equals(universalPartitionRepresentative);
			if (!isUniversal) {
				lettersNotInUniversalPartition.addAll(lettersNotInUniversalPartition);
				final DawgState middleState = mDawgStateFactory.createDawgState();
				final DawgLetter<LETTER> eqClassDl =
						mDawgLetterFactory.getSimpleDawgLetter(eqClass, sort);
				transitionRelation.put(initialState, eqClassDl, middleState);
				transitionRelation.put(middleState, eqClassDl, finalState);
			}
		}
		/*
		 * make transitions for the universal partition
		 */
		if (!lettersNotInUniversalPartition.isEmpty()) {
			final DawgState middleState = mDawgStateFactory.createDawgState();
			final DawgLetter<LETTER> complementDl =
					mDawgLetterFactory.getSimpleComplementDawgLetter(lettersNotInUniversalPartition, sort);
			transitionRelation.put(initialState, complementDl, middleState);
			transitionRelation.put(middleState, complementDl, finalState);
		}

		return new Dawg<LETTER, COLNAMES>(this, mLogger, inputDawg.getColNames(), transitionRelation, initialState);
	}

	/*
	 * this implementation does not seem to work --> perhaps restore it some time.. (using UnionFind based solution for
	 * now..)
	 */
	public Dawg<LETTER, COLNAMES> closeDawgUnderSymmetryAndTransitivityOld(final Dawg<LETTER, COLNAMES> inputDawg) {
		assert inputDawg.getSignature().getNoColumns() == 2;
		assert EprTheorySettings.UseSimpleDawgLetters;

		final DeterministicDawgTransitionRelation<DawgState, DawgLetter<LETTER>, DawgState> newTransitionRelation1 =
				new DeterministicDawgTransitionRelation<DawgState, DawgLetter<LETTER>, DawgState>();
		/*
		 * First, close under symmetry by replacing the dawgLetters at all two connected edges by their union. This may
		 * mean that outgoing DawgLetters are no more disjoint, but we will resolve this in the next step.. Can we lose
		 * information here by using a nested map?, i.e. do we need a relation?..
		 */
		for (final Pair<DawgLetter<LETTER>, DawgState> outEdge1 :
		inputDawg.getTransitionRelation().getOutEdgeSet(inputDawg.getInitialState())) {
			final DawgState outEdge1Target = outEdge1.getSecond();
			final DawgLetter<LETTER> outEdge1DL = outEdge1.getFirst();

			for (final Pair<DawgLetter<LETTER>, DawgState> outEdge2 :
			inputDawg.getTransitionRelation().getOutEdgeSet(outEdge1Target)) {
				final DawgState outEdge2Target = outEdge2.getSecond();
				final DawgLetter<LETTER> outEdge2DL = outEdge2.getFirst();

				final DawgLetter<LETTER> unionDL = outEdge1DL.union(outEdge2DL);

				/*
				 * add two edges replacing outEdge1 and outEdge2, each labelled with unionDL
				 */
				if (newTransitionRelation1.get(inputDawg.getInitialState(), unionDL) != null) {
					// assert newTransitionRelation1.get(inputDawg.getInitialState(), unionDL).equals(outEdge1Target);
				} else {
					newTransitionRelation1.put(inputDawg.getInitialState(), unionDL, outEdge1Target);
				}
				if (newTransitionRelation1.get(outEdge1Target, unionDL) != null) {
					// assert newTransitionRelation1.get(outEdge1Target, unionDL).equals(outEdge2Target);
				} else {
					newTransitionRelation1.put(outEdge1Target, unionDL, outEdge2Target);
				}

				// TODO: do we have to catch special cases here? like when two outEdge1 become the same??
			}
		}

		final DeterministicDawgTransitionRelation<DawgState, DawgLetter<LETTER>, DawgState>
		newTransitionRelation2 =
				new DeterministicDawgTransitionRelation<DawgState, DawgLetter<LETTER>, DawgState>();

		/*
		 * second, close under transitivity .. replace all pairs outgoing DawgLetters of the initial state by their that
		 * have a non-empty intersection by their union (there should be one pair of transitions per equivalence class
		 * in the dawg in the end..)
		 */
		final HashSet<Pair<DawgLetter<LETTER>, DawgState>> treatedOutEdges =
				new HashSet<Pair<DawgLetter<LETTER>, DawgState>>();
		for (final Pair<DawgLetter<LETTER>, DawgState> outEdge1 :
		inputDawg.getTransitionRelation().getOutEdgeSet(inputDawg.getInitialState())) {
			if (treatedOutEdges.contains(outEdge1)) {
				continue;
			}
			final DawgLetter<LETTER> outEdge1DL = outEdge1.getFirst();

			DawgLetter<LETTER> unionDlOfIntersectingOutEdges =
					mDawgLetterFactory.getEmptyDawgLetter(outEdge1DL.getSortId());
			for (final Pair<DawgLetter<LETTER>, DawgState> otherOutEdge1 :
			inputDawg.getTransitionRelation().getOutEdgeSet(inputDawg.getInitialState())) {
				final DawgLetter<LETTER> otherOutEdge1DL = outEdge1.getFirst();

				final DawgLetter<LETTER> intersectDl = outEdge1DL.intersect(otherOutEdge1DL);
				if (!intersectDl.isEmpty()) {
					treatedOutEdges.add(otherOutEdge1);
					unionDlOfIntersectingOutEdges = unionDlOfIntersectingOutEdges.union(otherOutEdge1DL);
				}
			}

			/*
			 * add two edges replacing all the intersecting edges
			 */
			final DawgState freshDawgState1 = mDawgStateFactory.createDawgState();
			final DawgState freshDawgState2 = mDawgStateFactory.createDawgState();
			newTransitionRelation2.put(inputDawg.getInitialState(), unionDlOfIntersectingOutEdges, freshDawgState1);
			newTransitionRelation2.put(freshDawgState1, unionDlOfIntersectingOutEdges, freshDawgState2);

		}

		return new Dawg<LETTER, COLNAMES>(this, mLogger, inputDawg.getColNames(), newTransitionRelation2,
				inputDawg.getInitialState());
	}


	/**
	 * Creates a dawg with the given signature (which needs to have exactly two columns) that recognizes all reflexive
	 * points that one can build over the currently known constants.
	 *
	 * @param signature
	 * @return
	 */
	public IDawg<LETTER, COLNAMES>
			getReflexivePointsOverCurrentlyKnownConstantsForSignature(final DawgSignature<COLNAMES> signature) {
		assert signature.getNoColumns() == 2;

		final Object sort = signature.getColumnSorts().get(0);
		assert signature.getColumnSorts().get(1).equals(sort) : "this is an equality dawg, right? "
				+ "so column sorts should match";

		final DawgState dsInitial = mDawgStateFactory.createDawgState();
		final DawgState dsFinal = mDawgStateFactory.createDawgState();

		final DeterministicDawgTransitionRelation<DawgState, DawgLetter<LETTER>, DawgState> newTR =
				new DeterministicDawgTransitionRelation<DawgState, DawgLetter<LETTER>, DawgState>();

		for (final LETTER constant : mAllKnownConstants.get(sort)) {
			final DawgState dsMiddle = mDawgStateFactory.createDawgState();
			final DawgLetter<LETTER> dl = mDawgLetterFactory.getSingletonSetDawgLetter(constant, sort);

			newTR.put(dsInitial, dl, dsMiddle);
			newTR.put(dsMiddle, dl, dsFinal);
		}

		return new Dawg<LETTER, COLNAMES>(this, mLogger, signature.getColNames(), newTR, dsInitial);
	}

}
