package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Random;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;

/**
 * This class provides several heuristics for choosing MUSes or groups of MUSes for Interpolant generation.
 *
 * @author LeonardFichtner (leonard.fichtner@web.de)
 *
 */
public class Heuristics {

	private enum ResultOfComparison {
		MUS1 {
		},
		MUS2 {
		},
		EQUAL {
		}
	}

	/**
	 * Chooses a random MusContainer from the given ArrayList and returns it. Returns null if the given list is emtpy.
	 */
	public static MusContainer chooseRandomMus(final ArrayList<MusContainer> muses, final Random rnd) {
		if (muses.isEmpty()) {
			return null;
		}
		return muses.get(rnd.nextInt(muses.size()));
	}

	/**
	 * Chooses the the smallest Mus (in terms of cardinality) from the given ArrayList and returns its MusContainer. In
	 * case there are multiple such muses, this algorithm randomly chooses one of them. Returns null if the given list
	 * is empty.
	 */
	public static MusContainer chooseSmallestMus(final ArrayList<MusContainer> muses, final Random rnd) {
		if (muses.isEmpty()) {
			return null;
		}
		return chooseRandomMus(findBestMusesAccordingToGivenCriterion(muses, Heuristics::compareWhichMusIsSmaller),
				rnd);
	}

	/**
	 * Chooses the biggest Mus (in terms of cardinality) from the given ArrayList and returns its MusContainer. In case
	 * there are multiple such muses, this algorithm randomly chooses one of them. Returns null if the given list is
	 * empty.
	 */
	public static MusContainer chooseBiggestMus(final ArrayList<MusContainer> muses, final Random rnd) {
		if (muses.isEmpty()) {
			return null;
		}
		return chooseRandomMus(findBestMusesAccordingToGivenCriterion(muses, Heuristics::compareWhichMusIsBigger), rnd);
	}

	/**
	 * Chooses the Mus with the lowest Lexicographical order (in terms of indices of the contained constraints) from the
	 * given ArrayList and returns its MusContainer. Returns null if List is empty.
	 */
	public static MusContainer chooseMusWithLowestLexicographicalOrder(final ArrayList<MusContainer> muses,
			final Random rnd) {
		if (muses.isEmpty()) {
			return null;
		}
		return chooseRandomMus(
				findBestMusesAccordingToGivenCriterion(muses, Heuristics::compareWhichMusHasLowerLexicographicalOrder),
				rnd);
	}

	/**
	 * Chooses the Mus with the highest Lexicographical order (in terms of indices of the contained constraints) from
	 * the given ArrayList and returns its MusContainer. Returns null if the given list is empty.
	 */
	public static MusContainer chooseMusWithHighestLexicographicalOrder(final ArrayList<MusContainer> muses,
			final Random rnd) {
		if (muses.isEmpty()) {
			return null;
		}
		return chooseRandomMus(
				findBestMusesAccordingToGivenCriterion(muses, Heuristics::compareWhichMusHasHigherLexicographicalOrder),
				rnd);
	}

	/**
	 * Chooses the shallowest Mus of the given ArrayList and returns its MusContainer. In case there are multiple such
	 * muses, this algorithm randomly chooses one of them. Shallow here means, that the first constraint of the mus has
	 * a low index. Returns null if the given list is empty.
	 */
	public static MusContainer chooseShallowestMus(final ArrayList<MusContainer> muses, final Random rnd) {
		if (muses.isEmpty()) {
			return null;
		}
		return chooseRandomMus(findBestMusesAccordingToGivenCriterion(muses, Heuristics::compareWhichMusIsShallowerMus),
				rnd);
	}

	/**
	 * Chooses the deepest Mus of the given ArrayList and returns its MusContainer. In case there are multiple such
	 * muses, this algorithm randomly chooses one of them. Deep here means, that the first constraint of the mus has a
	 * high index. Returns null if the given list is empty.
	 */
	public static MusContainer chooseDeepestMus(final ArrayList<MusContainer> muses, final Random rnd) {
		if (muses.isEmpty()) {
			return null;
		}
		return chooseRandomMus(findBestMusesAccordingToGivenCriterion(muses, Heuristics::compareWhichMusIsDeeperMus),
				rnd);
	}

	/**
	 * Chooses the narrowest Mus of the given ArrayList and returns its MusContainer. In case there are multiple such
	 * muses, this algorithm randomly chooses one of them. Narrow here means, that the difference between the highest
	 * index of a constraint in the mus and the lowest index of a constraint in the mus is small. Returns null if the
	 * given list is empty.
	 */
	public static MusContainer chooseNarrowestMus(final ArrayList<MusContainer> muses, final Random rnd) {
		if (muses.isEmpty()) {
			return null;
		}
		return chooseRandomMus(findBestMusesAccordingToGivenCriterion(muses, Heuristics::compareWhichMusIsNarrowerMus),
				rnd);
	}

	/**
	 * Chooses the widest Mus of the given ArrayList and returns its MusContainer. In case there are multiple such
	 * muses, this algorithm randomly chooses one of them. Wide here means, that the difference between the highest
	 * index of a constraint in the mus and the lowest index of a constraint in the mus is big. Returns null if the
	 * given list is empty.
	 */
	public static MusContainer chooseWidestMus(final ArrayList<MusContainer> muses, final Random rnd) {
		if (muses.isEmpty()) {
			return null;
		}
		return chooseRandomMus(findBestMusesAccordingToGivenCriterion(muses, Heuristics::compareWhichMusIsWiderMus),
				rnd);
	}

	/**
	 * First selects the widest Muses of the given ArrayList. Tolerance specifies which muses count as "widest" - to be
	 * precise a mus counts as widest when widthOf(mus) >= (1-tolerance)*maximumWidthOfMuses(muses). Afterwards, the
	 * smallest Mus amongst the widest muses is returned. In case there are multiple such muses, this algorithm randomly
	 * chooses one of them. Returns null if the given list is empty.
	 */
	public static MusContainer chooseSmallestAmongWidestMus(final ArrayList<MusContainer> muses, final double tolerance,
			final Random rnd) {
		if (muses.isEmpty()) {
			return null;
		}
		final ArrayList<MusContainer> widestMuses = new ArrayList<>();
		final MusContainer widestMus = chooseWidestMus(muses, rnd);
		final int maximalOccurringWidth = widestMus.getMus().length() - widestMus.getMus().nextSetBit(0);
		int currentWidth;
		for (final MusContainer container : muses) {
			currentWidth = container.getMus().length() - container.getMus().nextSetBit(0);
			if (currentWidth >= (1 - tolerance) * maximalOccurringWidth) {
				widestMuses.add(container);
			}
		}
		return chooseSmallestMus(widestMuses, rnd);
	}

	/**
	 * First selects the smallest Muses of the given ArrayList. Tolerance specifies which muses count as "smallest" - to
	 * be precise a mus counts as smallest when sizeOf(mus) >= (1-tolerance)*maximumSizeOfMuses(muses). Afterwards, the
	 * widest Mus amongst the smallest muses is returned. In case there are multiple such muses, this algorithm randomly
	 * chooses one of them. Returns null if the given list is empty.
	 */
	public static MusContainer chooseWidestAmongSmallestMus(final ArrayList<MusContainer> muses, final double tolerance,
			final Random rnd) {
		if (muses.isEmpty()) {
			return null;
		}
		final ArrayList<MusContainer> smallestMuses = new ArrayList<>();
		final MusContainer smallestMus = chooseSmallestMus(muses, rnd);
		final int minimalOccurringSize = smallestMus.getMus().cardinality();
		int currentSize;
		for (final MusContainer container : muses) {
			currentSize = container.getMus().length() - container.getMus().nextSetBit(0);
			if (currentSize >= (1 - tolerance) * minimalOccurringSize) {
				smallestMuses.add(container);
			}
		}
		return chooseWidestMus(smallestMuses, rnd);
	}

	/**
	 * This is here for documentary purpose and also maybe for use as FunctionalInterface later on.
	 */
	public static ArrayList<MusContainer> chooseAllMuses(final ArrayList<MusContainer> muses) {
		return muses;
	}

	/**
	 * This returns the most extreme muses in terms of the other heuristics in this class that return a single mus.
	 */
	public static ArrayList<MusContainer> chooseMostDifferentMusesWithRespectToOtherHeuristics(
			final ArrayList<MusContainer> muses, final Random rnd) {
		if (muses.isEmpty()) {
			return new ArrayList<>();
		}
		final ArrayList<MusContainer> mostExtremeMuses = new ArrayList<>();
		// ignore Random
		mostExtremeMuses.add(chooseSmallestMus(muses, rnd));
		mostExtremeMuses.add(chooseBiggestMus(muses, rnd));
		mostExtremeMuses.add(chooseMusWithLowestLexicographicalOrder(muses, rnd));
		mostExtremeMuses.add(chooseMusWithHighestLexicographicalOrder(muses, rnd));
		mostExtremeMuses.add(chooseShallowestMus(muses, rnd));
		mostExtremeMuses.add(chooseDeepestMus(muses, rnd));
		mostExtremeMuses.add(chooseNarrowestMus(muses, rnd));
		mostExtremeMuses.add(chooseWidestMus(muses, rnd));
		mostExtremeMuses.add(chooseSmallestAmongWidestMus(muses, 0.9, rnd));
		mostExtremeMuses.add(chooseWidestAmongSmallestMus(muses, 0.9, rnd));
		return mostExtremeMuses;
	}

	/**
	 * For a given set of muses and a random number generator, returns an ArrayList of {@link MusContainer} which muses
	 * are as different as possible. More specifically, at the beginning a random mus is chosen. Afterwards, a loop is
	 * executed until the given size is reached. The loop finds the mus which maximizes the minimum number of different
	 * statements {@link #numberOfDifferentStatements(MusContainer, MusContainer)} between itself and the muses that
	 * have already been chosen to be in the list that will be returned. Note that the returned list will not contain
	 * duplicates, hence it could be smaller than the given size.
	 */
	public static ArrayList<MusContainer> chooseDifferentMusesWithRespectToStatements(
			final ArrayList<MusContainer> muses, final int size, final Random rnd) {
		if (muses.isEmpty() || size == 0) {
			return new ArrayList<>();
		}
		final ArrayList<MusContainer> differentMuses = new ArrayList<>();
		final ArrayList<MusContainer> maxMinDifferenceMuses = new ArrayList<>();
		differentMuses.add(muses.get(rnd.nextInt(muses.size())));
		int maxMinDifference;
		int currentMinDifference;
		for (int i = 1; i < size; i++) {
			maxMinDifference = Integer.MIN_VALUE;
			for (final MusContainer contender : muses) {
				currentMinDifference = findMinimumNumberOfDifferentStatements(contender, differentMuses);
				if (currentMinDifference > maxMinDifference) {
					maxMinDifference = currentMinDifference;
					maxMinDifferenceMuses.clear();
					maxMinDifferenceMuses.add(contender);
				} else if (currentMinDifference == maxMinDifference) {
					maxMinDifferenceMuses.add(contender);
				}
			}
			if (maxMinDifference == 0) {
				// This means maxMinDifferenceMus is a duplicate
				break;
			}
			differentMuses.add(chooseRandomMus(maxMinDifferenceMuses, rnd));
		}
		return differentMuses;
	}

	/**
	 * Find the minimum number of different statements (the minimum Hamming distance) between the given mus1 and some
	 * mus of the given list of muses.
	 */
	private static int findMinimumNumberOfDifferentStatements(final MusContainer mus1,
			final ArrayList<MusContainer> muses) {
		int currentDifference;
		int minimumDifference = Integer.MAX_VALUE;
		for (final MusContainer mus2 : muses) {
			currentDifference = numberOfDifferentStatements(mus1, mus2);
			if (currentDifference < minimumDifference) {
				minimumDifference = currentDifference;
			}
		}
		return minimumDifference;
	}

	/**
	 * Returns the number of different statements of the two muses (hence, the Hamming distance).
	 */
	public static int numberOfDifferentStatements(final MusContainer mus1, final MusContainer mus2) {
		final BitSet realMus1 = mus1.getMus();
		final BitSet realMus2 = mus2.getMus();
		int difference = 0;
		for (int i = 0; i < realMus1.length(); i++) {
			if ((realMus1.get(i) && !realMus2.get(i)) || (realMus2.get(i) && !realMus1.get(i))) {
				difference++;
			}
		}
		if (realMus2.length() > realMus1.length()) {
			for (int i = realMus2.nextSetBit(realMus1.length()); i >= 0; i = realMus2.nextSetBit(i + 1)) {
				difference++;
			}
		}
		return difference;
	}

	private static ResultOfComparison compareWhichMusIsSmaller(final MusContainer mus1, final MusContainer mus2) {
		final int length1 = mus1.getMus().cardinality();
		final int length2 = mus2.getMus().cardinality();
		if (length1 < length2) {
			return ResultOfComparison.MUS1;
		} else if (length1 > length2) {
			return ResultOfComparison.MUS2;
		} else {
			return ResultOfComparison.EQUAL;
		}
	}

	private static ResultOfComparison compareWhichMusIsBigger(final MusContainer mus1, final MusContainer mus2) {
		return compareWhichMusIsSmaller(mus2, mus1);
	}

	private static ResultOfComparison compareWhichMusHasLowerLexicographicalOrder(final MusContainer mus1,
			final MusContainer mus2) {
		final BitSet realMus1 = mus1.getMus();
		final BitSet realMus2 = mus2.getMus();
		for (int i = 0; i < realMus1.length(); i++) {
			if (realMus1.get(i)) {
				if (!realMus2.get(i)) {
					return ResultOfComparison.MUS1;
				}
			} else {
				if (realMus2.get(i)) {
					return ResultOfComparison.MUS2;
				}
			}
		}
		if (realMus2.length() > realMus1.length()) {
			return ResultOfComparison.MUS1;
		}
		throw new SMTLIBException("Both muses must be the same. This should not be.");
	}

	private static ResultOfComparison compareWhichMusHasHigherLexicographicalOrder(final MusContainer mus1,
			final MusContainer mus2) {
		if (compareWhichMusHasLowerLexicographicalOrder(mus1, mus2) == ResultOfComparison.MUS1) {
			return ResultOfComparison.MUS2;
		}
		return ResultOfComparison.MUS1;
	}

	private static ResultOfComparison compareWhichMusIsShallowerMus(final MusContainer mus1, final MusContainer mus2) {
		final int depth1 = mus1.getMus().nextSetBit(0);
		final int depth2 = mus2.getMus().nextSetBit(0);
		if (depth1 < depth2) {
			return ResultOfComparison.MUS1;
		} else if (depth1 > depth2) {
			return ResultOfComparison.MUS2;
		} else {
			return ResultOfComparison.EQUAL;
		}
	}

	private static ResultOfComparison compareWhichMusIsDeeperMus(final MusContainer mus1, final MusContainer mus2) {
		return compareWhichMusIsShallowerMus(mus2, mus1);
	}

	private static ResultOfComparison compareWhichMusIsNarrowerMus(final MusContainer mus1, final MusContainer mus2) {
		final int width1 = mus1.getMus().length() - mus1.getMus().nextSetBit(0);
		final int width2 = mus2.getMus().length() - mus2.getMus().nextSetBit(0);
		if (width1 < width2) {
			return ResultOfComparison.MUS1;
		} else if (width1 > width2) {
			return ResultOfComparison.MUS2;
		} else {
			return ResultOfComparison.EQUAL;
		}
	}

	private static ResultOfComparison compareWhichMusIsWiderMus(final MusContainer mus1, final MusContainer mus2) {
		return compareWhichMusIsNarrowerMus(mus2, mus1);
	}

	private static ArrayList<MusContainer> findBestMusesAccordingToGivenCriterion(final ArrayList<MusContainer> muses,
			final BiFunction<MusContainer, MusContainer, ResultOfComparison> criterion) {
		final ArrayList<MusContainer> bestMuses = new ArrayList<>();
		MusContainer oneOfTheBestMuses = muses.get(0);
		bestMuses.add(oneOfTheBestMuses);
		MusContainer contender;
		ResultOfComparison result;
		for (int i = 1; i < muses.size(); i++) {
			contender = muses.get(i);
			result = criterion.apply(oneOfTheBestMuses, contender);
			if (result == ResultOfComparison.MUS2) {
				bestMuses.clear();
				bestMuses.add(contender);
				oneOfTheBestMuses = contender;
			} else if (result == ResultOfComparison.EQUAL) {
				bestMuses.add(contender);
			}
		}
		return bestMuses;
	}
}
