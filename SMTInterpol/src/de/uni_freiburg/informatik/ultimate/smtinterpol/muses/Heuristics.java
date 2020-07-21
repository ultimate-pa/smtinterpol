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
		return findBestMusAccordingToGivenCriterion(smallestMuses, Heuristics::returnSmallerMus);
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
	 * This returns muses which are as different as possible in terms of statements contained. Since it would be an
	 * expensive task to maximize the differences of all the muses that should be returned, this method relies on on
	 * randomness to achieve an acceptable result. More precisely, it chooses a random mus and then finds a mus that has
	 * the maximal number of different constraints. In case there are multiple such muses, this algorithm takes the last
	 * one that has been found. The two muses will then be added to the list, that will be returned at the end of the
	 * procedure. The given int "samples" specifies how many times this procedure is iterated, before returning the list
	 * that has been built. Note, that the returned list will not necessarily have "samples"-many elements, since it
	 * could be that the same muses have been selected randomly and duplicates in the returned list are filtered out.
	 */
	public static ArrayList<MusContainer>
			chooseMostDifferentMusesWithRespectToStatements(final ArrayList<MusContainer> muses, final int samples) {
		if (muses.isEmpty()) {
			return new ArrayList<>();
		}
		final ArrayList<MusContainer> differentMuses = new ArrayList<>();
		final Random rnd = new Random(1337);
		MusContainer randomContainer;
		int difference;
		int currentDifference;
		MusContainer mostDifferentContainer = null;
		for (int i = 0; i <= samples; i++) {
			randomContainer = muses.get(rnd.nextInt(muses.size()));
			if (differentMuses.contains(randomContainer)) {
				continue;
			}
			difference = 0;
			currentDifference = 0;
			for (final MusContainer container : muses) {
				currentDifference = numberOfDifferentStatements(randomContainer, container);
				if (difference <= currentDifference) {
					mostDifferentContainer = container;
					difference = currentDifference;
				}
			}
			if (mostDifferentContainer == null) {
				throw new SMTLIBException("Somehow no different container could be found.");
			}
			differentMuses.add(mostDifferentContainer);
		}
		return differentMuses;
	}

	private static int numberOfDifferentStatements(final MusContainer mus1, final MusContainer mus2) {
		final BitSet realMus1 = mus1.getMus();
		final BitSet realMus2 = mus2.getMus();
		int difference = 0;
		for (int i = realMus1.nextSetBit(0); i >= 0; i = realMus1.nextSetBit(i + 1)) {
			if (!realMus2.get(i)) {
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
