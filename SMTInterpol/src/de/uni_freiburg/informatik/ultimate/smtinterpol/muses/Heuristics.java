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

	/**
	 * Chooses a random MusContainer from the given ArrayList and returns it. Returns null if the List is emtpy.
	 */
	public static MusContainer chooseRandomMus(final ArrayList<MusContainer> muses, final long seed) {
		if (muses.isEmpty()) {
			return null;
		}
		final Random rnd = new Random(seed);
		return muses.get(rnd.nextInt(muses.size()));
	}

	/**
	 * Chooses the smallest Mus (in terms of cardinality) from the given ArrayList and returns its MusContainer. In case
	 * there are multiple such muses, this algorithm takes the last one that has been found. Returns null if List is
	 * empty.
	 */
	public static MusContainer chooseSmallestMus(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		return findBestMusAccordingToGivenCriterion(muses, Heuristics::returnSmallerMus);
	}

	/**
	 * Chooses the biggest Mus (in terms of cardinality) from the given ArrayList and returns its MusContainer. In case
	 * there are multiple such muses, this algorithm takes the last one that has been found. Returns null if List is
	 * empty.
	 */
	public static MusContainer chooseBiggestMus(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		return findBestMusAccordingToGivenCriterion(muses, Heuristics::returnBiggerMus);
	}

	/**
	 * Chooses the Mus with the lowest Lexicographical order (in terms of indices of the contained constraints) from the
	 * given ArrayList and returns its MusContainer. Returns null if List is empty.
	 */
	public static MusContainer chooseMusWithLowestLexicographicalOrder(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		return findBestMusAccordingToGivenCriterion(muses, Heuristics::returnMusWithLowerLexicographicalOrder);
	}

	/**
	 * Chooses the Mus with the highest Lexicographical order (in terms of indices of the contained constraints) from
	 * the given ArrayList and returns its MusContainer. Returns null if List is empty.
	 */
	public static MusContainer chooseMusWithHighestLexicographicalOrder(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		return findBestMusAccordingToGivenCriterion(muses, Heuristics::returnMusWithHigherLexicographicalOrder);
	}

	/**
	 * Chooses the shallowest Mus of the given ArrayList and returns its MusContainer. In case there are multiple such
	 * muses, this algorithm takes the last one that has been found. Shallow here means, that the first constraint of
	 * the mus has a low index. Returns null if List is empty.
	 */
	public static MusContainer chooseShallowestMus(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		return findBestMusAccordingToGivenCriterion(muses, Heuristics::returnShallowerMus);
	}

	/**
	 * Chooses the deepest Mus of the given ArrayList and returns its MusContainer. In case there are multiple such
	 * muses, this algorithm takes the last one that has been found. Deep here means, that the first constraint of the
	 * mus has a high index. Returns null if List is empty.
	 */
	public static MusContainer chooseDeepestMus(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		return findBestMusAccordingToGivenCriterion(muses, Heuristics::returnDeeperMus);
	}

	/**
	 * Chooses the narrowest Mus of the given ArrayList and returns its MusContainer. In case there are multiple such
	 * muses, this algorithm takes the last one that has been found. Narrow here means, that the difference between the
	 * highest index of a constraint in the mus and the lowest index of a constraint in the mus is small. Returns null
	 * if List is empty.
	 */
	public static MusContainer chooseNarrowestMus(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		return findBestMusAccordingToGivenCriterion(muses, Heuristics::returnNarrowerMus);
	}

	/**
	 * Chooses the widest Mus of the given ArrayList and returns its MusContainer. In case there are multiple such
	 * muses, this algorithm takes the last one that has been found. Wide here means, that the difference between the
	 * highest index of a constraint in the mus and the lowest index of a constraint in the mus is big. Returns null if
	 * List is empty.
	 */
	public static MusContainer chooseWidestMus(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		return findBestMusAccordingToGivenCriterion(muses, Heuristics::returnWiderMus);
	}

	/**
	 * First selects the widest Muses of the given ArrayList. Tolerance specifies which muses count as "widest" - to be
	 * precise a mus counts as widest when widthOf(mus) >= (1-tolerance)*maximumWidthOfMuses(muses). Afterwards, the
	 * smallest Mus amongst the widest muses is returned. In case there are multiple such muses, this algorithm takes
	 * the last one that has been found. Returns null if List is empty.
	 */
	public static MusContainer chooseSmallestAmongWidestMus(final ArrayList<MusContainer> muses,
			final double tolerance) {
		if (muses.isEmpty()) {
			return null;
		}
		final ArrayList<MusContainer> widestMuses = new ArrayList<>();
		final MusContainer widestMus = findBestMusAccordingToGivenCriterion(muses, Heuristics::returnWiderMus);
		final int maximalOccurringWidth = widestMus.getMus().length() - widestMus.getMus().nextSetBit(0);
		int currentWidth;
		for (final MusContainer container : muses) {
			currentWidth = container.getMus().length() - container.getMus().nextSetBit(0);
			if (currentWidth >= (1 - tolerance) * maximalOccurringWidth) {
				widestMuses.add(container);
			}
		}
		return findBestMusAccordingToGivenCriterion(widestMuses, Heuristics::returnSmallerMus);
	}

	/**
	 * First selects the smallest Muses of the given ArrayList. Tolerance specifies which muses count as "smallest" - to
	 * be precise a mus counts as smallest when sizeOf(mus) >= (1-tolerance)*maximumSizeOfMuses(muses). Afterwards, the
	 * widest Mus amongst the smallest muses is returned. In case there are multiple such muses, this algorithm takes
	 * the last one that has been found. Returns null if List is empty.
	 */
	public static MusContainer chooseWidestAmongSmallestMus(final ArrayList<MusContainer> muses,
			final double tolerance) {
		if (muses.isEmpty()) {
			return null;
		}
		final ArrayList<MusContainer> smallestMuses = new ArrayList<>();
		final MusContainer smallestMus = findBestMusAccordingToGivenCriterion(muses, Heuristics::returnSmallerMus);
		final int minimalOccurringSize = smallestMus.getMus().cardinality();
		int currentSize;
		for (final MusContainer container : muses) {
			currentSize = container.getMus().length() - container.getMus().nextSetBit(0);
			if (currentSize >= (1 - tolerance) * minimalOccurringSize) {
				smallestMuses.add(container);
			}
		}
		return findBestMusAccordingToGivenCriterion(smallestMuses, Heuristics::returnWiderMus);
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
	public static ArrayList<MusContainer>
			chooseMostDifferentMusesWithRespectToOtherHeuristics(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return new ArrayList<>();
		}
		final ArrayList<MusContainer> mostExtremeMuses = new ArrayList<>();
		// ignore Random
		mostExtremeMuses.add(chooseSmallestMus(muses));
		mostExtremeMuses.add(chooseBiggestMus(muses));
		mostExtremeMuses.add(chooseMusWithLowestLexicographicalOrder(muses));
		mostExtremeMuses.add(chooseMusWithHighestLexicographicalOrder(muses));
		mostExtremeMuses.add(chooseShallowestMus(muses));
		mostExtremeMuses.add(chooseDeepestMus(muses));
		mostExtremeMuses.add(chooseNarrowestMus(muses));
		mostExtremeMuses.add(chooseWidestMus(muses));
		mostExtremeMuses.add(chooseSmallestAmongWidestMus(muses, 0.9));
		mostExtremeMuses.add(chooseWidestAmongSmallestMus(muses, 0.9));
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
		differentMuses.add(muses.get(rnd.nextInt(muses.size())));
		int maxMinDifference;
		int currentMinDifference;
		MusContainer maxMinDifferenceMus = null;
		for (int i = 1; i < size; i++) {
			maxMinDifference = Integer.MIN_VALUE;
			for (final MusContainer contender : muses) {
				currentMinDifference = findMinimumNumberOfDifferentStatements(contender, differentMuses);
				if (currentMinDifference > maxMinDifference) {
					maxMinDifference = currentMinDifference;
					maxMinDifferenceMus = contender;
				}
			}
			if (maxMinDifference == 0) {
				//This means maxMinDifferenceMus is a duplicate
				break;
			}
			differentMuses.add(maxMinDifferenceMus);
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

	private static MusContainer returnSmallerMus(final MusContainer mus1, final MusContainer mus2) {
		return mus1.getMus().cardinality() < mus2.getMus().cardinality() ? mus1 : mus2;
	}

	private static MusContainer returnBiggerMus(final MusContainer mus1, final MusContainer mus2) {
		return mus1.getMus().cardinality() > mus2.getMus().cardinality() ? mus1 : mus2;
	}

	private static MusContainer returnMusWithLowerLexicographicalOrder(final MusContainer mus1,
			final MusContainer mus2) {
		final BitSet realMus1 = mus1.getMus();
		final BitSet realMus2 = mus2.getMus();
		for (int i = 0; i < realMus1.length(); i++) {
			if (realMus1.get(i)) {
				if (!realMus2.get(i)) {
					return mus1;
				}
			} else {
				if (realMus2.get(i)) {
					return mus2;
				}
			}
		}
		if (realMus2.length() > realMus1.length()) {
			return mus1;
		}
		throw new SMTLIBException("Both muses must be the same. This should not be.");
	}

	private static MusContainer returnMusWithHigherLexicographicalOrder(final MusContainer mus1,
			final MusContainer mus2) {
		if (returnMusWithLowerLexicographicalOrder(mus1, mus2).getMus().equals(mus1.getMus())) {
			return mus2;
		}
		return mus1;
	}

	private static MusContainer returnShallowerMus(final MusContainer mus1, final MusContainer mus2) {
		return mus1.getMus().nextSetBit(0) < mus2.getMus().nextSetBit(0) ? mus1 : mus2;
	}

	private static MusContainer returnDeeperMus(final MusContainer mus1, final MusContainer mus2) {
		return mus1.getMus().nextSetBit(0) > mus2.getMus().nextSetBit(0) ? mus1 : mus2;
	}

	private static MusContainer returnNarrowerMus(final MusContainer mus1, final MusContainer mus2) {
		final int width1 = mus1.getMus().length() - mus1.getMus().nextSetBit(0);
		final int width2 = mus2.getMus().length() - mus2.getMus().nextSetBit(0);
		return width1 < width2 ? mus1 : mus2;
	}

	private static MusContainer returnWiderMus(final MusContainer mus1, final MusContainer mus2) {
		final int width1 = mus1.getMus().length() - mus1.getMus().nextSetBit(0);
		final int width2 = mus2.getMus().length() - mus2.getMus().nextSetBit(0);
		return width1 > width2 ? mus1 : mus2;
	}

	private static MusContainer findBestMusAccordingToGivenCriterion(final ArrayList<MusContainer> muses,
			final BiFunction<MusContainer, MusContainer, MusContainer> criterion) {
		MusContainer bestMus = muses.get(0);
		MusContainer contender;
		for (int i = 1; i < muses.size(); i++) {
			contender = muses.get(i);
			bestMus = criterion.apply(bestMus, contender);
		}
		return bestMus;
	}
}
