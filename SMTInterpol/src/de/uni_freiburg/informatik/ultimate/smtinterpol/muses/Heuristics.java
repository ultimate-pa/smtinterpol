package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Random;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;

/**
 * This class provides several heuristics for choosing MUSes or groups of MUSes for Interpolant generation.
 *
 * @author LeonardFichtner
 *
 */
public class Heuristics {

	/**
	 * Chooses a random MusContainer from the given ArrayList and returns it. Returns null if the List is emtpy.
	 */
	public static MusContainer chooseRandomMus(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		final Random rnd = new Random(1337);
		return muses.get(rnd.nextInt(muses.size()));
	}

	/**
	 * Chooses the smallest Mus (in terms of cardinality) from the given ArrayList and returns its MusContainer. Returns
	 * null if List is empty.
	 */
	public static MusContainer chooseSmallestMus(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		return findBestMusAccordingToGivenMetric(muses, Heuristics::returnSmallerMus);
	}

	/**
	 * Chooses the biggest Mus (in terms of cardinality) from the given ArrayList and returns its MusContainer. Returns
	 * null if List is empty.
	 */
	public static MusContainer chooseBiggestMus(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		return findBestMusAccordingToGivenMetric(muses, Heuristics::returnBiggerMus);
	}

	/**
	 * Chooses the Mus with the lowest Lexicographical order (in terms of indices of the contained constraints) from the
	 * given ArrayList and returns its MusContainer. Returns null if List is empty.
	 */
	public static MusContainer chooseMusWithLowestLexicographicalOrder(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		return findBestMusAccordingToGivenMetric(muses, Heuristics::returnMusWithLowerLexicographicalOrder);
	}

	/**
	 * Chooses the Mus with the highest Lexicographical order (in terms of indices of the contained constraints) from
	 * the given ArrayList and returns its MusContainer. Returns null if List is empty.
	 */
	public static MusContainer chooseMusWithHighestLexicographicalOrder(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		return findBestMusAccordingToGivenMetric(muses, Heuristics::returnMusWithHigherLexicographicalOrder);
	}

	/**
	 * Chooses the shallowest Mus of the given ArrayList and returns its MusContainer. Shallow here means, that the
	 * first constraint of the mus has a low index. Returns null if List is empty.
	 */
	public static MusContainer chooseShallowestMus(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		return findBestMusAccordingToGivenMetric(muses, Heuristics::returnShallowerMus);
	}

	/**
	 * Chooses the deepest Mus of the given ArrayList and returns its MusContainer. Deep here means, that the first
	 * constraint of the mus has a high index. Returns null if List is empty.
	 */
	public static MusContainer chooseDeepestMus(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		return findBestMusAccordingToGivenMetric(muses, Heuristics::returnDeeperMus);
	}

	/**
	 * Chooses the narrowest Mus of the given ArrayList and returns its MusContainer. Narrow here means, that the
	 * difference between the highest index of a constraint in the mus and the lowest index of a constraint in the mus
	 * is small. Returns null if List is empty.
	 */
	public static MusContainer chooseNarrowestMus(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		return findBestMusAccordingToGivenMetric(muses, Heuristics::returnNarrowerMus);
	}

	/**
	 * Chooses the widest Mus of the given ArrayList and returns its MusContainer. Wide here means, that the difference
	 * between the highest index of a constraint in the mus and the lowest index of a constraint in the mus is big.
	 * Returns null if List is empty.
	 */
	public static MusContainer chooseWidestMus(final ArrayList<MusContainer> muses) {
		if (muses.isEmpty()) {
			return null;
		}
		return findBestMusAccordingToGivenMetric(muses, Heuristics::returnWiderMus);
	}

	/**
	 * First selects the widest Muses of the given ArrayList. Tolerance specifies which muses count as "widest" - to be
	 * precise a mus counts as widest when widthOf(mus) >= (1-tolerance)*maximumWidthOfMuses(muses). Afterwards, the
	 * smallest Mus amongst the widest muses is returned. Returns null if List is empty.
	 */
	public static MusContainer chooseSmallestAmongWidestMus(final ArrayList<MusContainer> muses, final int tolerance) {
		if (muses.isEmpty()) {
			return null;
		}
		final ArrayList<MusContainer> widestMuses = new ArrayList<>();
		final MusContainer widestMus = findBestMusAccordingToGivenMetric(muses, Heuristics::returnWiderMus);
		final int maximalOccurringWidth = widestMus.getMus().length() - widestMus.getMus().nextSetBit(0);
		int currentWidth;
		for (final MusContainer container : muses) {
			currentWidth = container.getMus().length() - container.getMus().nextSetBit(0);
			if (currentWidth >= (1 - tolerance) * maximalOccurringWidth) {
				widestMuses.add(container);
			}
		}
		return findBestMusAccordingToGivenMetric(widestMuses, Heuristics::returnSmallerMus);
	}

	/**
	 * First selects the smallest Muses of the given ArrayList. Tolerance specifies which muses count as "smallest" - to
	 * be precise a mus counts as smallest when sizeOf(mus) >= (1-tolerance)*maximumSizeOfMuses(muses). Afterwards, the
	 * widest Mus amongst the smallest muses is returned. Returns null if List is empty.
	 */
	public static MusContainer chooseWidestAmongstSmallest(final ArrayList<MusContainer> muses, final int tolerance) {
		if (muses.isEmpty()) {
			return null;
		}
		final ArrayList<MusContainer> smallestMuses = new ArrayList<>();
		final MusContainer smallestMus = findBestMusAccordingToGivenMetric(muses, Heuristics::returnSmallerMus);
		final int minimalOccurringSize = smallestMus.getMus().cardinality();
		int currentSize;
		for (final MusContainer container : muses) {
			currentSize = container.getMus().length() - container.getMus().nextSetBit(0);
			if (currentSize >= (1 - tolerance) * minimalOccurringSize) {
				smallestMuses.add(container);
			}
		}
		return findBestMusAccordingToGivenMetric(smallestMuses, Heuristics::returnSmallerMus);
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
		if (mus1.getMus().nextSetBit(0) < mus2.getMus().nextSetBit(0)) {
			return mus1;
		}
		return mus2;
	}

	private static MusContainer returnDeeperMus(final MusContainer mus1, final MusContainer mus2) {
		if (mus1.getMus().nextSetBit(0) > mus2.getMus().nextSetBit(0)) {
			return mus1;
		}
		return mus2;
	}

	private static MusContainer returnNarrowerMus(final MusContainer mus1, final MusContainer mus2) {
		final int width1 = mus1.getMus().length() - mus1.getMus().nextSetBit(0);
		final int width2 = mus2.getMus().length() - mus2.getMus().nextSetBit(0);
		if (width1 < width2) {
			return mus1;
		}
		return mus2;
	}

	private static MusContainer returnWiderMus(final MusContainer mus1, final MusContainer mus2) {
		final int width1 = mus1.getMus().length() - mus1.getMus().nextSetBit(0);
		final int width2 = mus2.getMus().length() - mus2.getMus().nextSetBit(0);
		if (width1 > width2) {
			return mus1;
		}
		return mus2;
	}

	private static MusContainer findBestMusAccordingToGivenMetric(final ArrayList<MusContainer> muses,
			final BiFunction<MusContainer, MusContainer, MusContainer> metric) {
		MusContainer bestMus = muses.get(0);
		MusContainer contender;
		for (int i = 1; i < muses.size(); i++) {
			contender = muses.get(i);
			bestMus = metric.apply(bestMus, contender);
		}
		return bestMus;
	}
}
