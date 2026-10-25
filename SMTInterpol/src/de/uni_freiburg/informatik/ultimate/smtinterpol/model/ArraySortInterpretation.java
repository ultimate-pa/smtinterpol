/*
 * Copyright (C) 2014 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * The interpretation of an array sort. Array values are normalized, so that two arrays are equal if and only if their
 * values are the same term.
 *
 * <p>
 * Usually an array value is a chain of stores over a const array. For the piecewise-constant models of quantified
 * formulas, an array with a numeric index sort can also be piecewise constant: {@code (.as-array (lambda ((@i Int))
 * (ite (>= @i 5) v2 (ite (>= @i 3) v1 v0))))}. Such an array is printed as stores over a const array if it differs
 * from its default only at finitely many points, and as {@code .as-array} of a first-match {@code ite} chain over its
 * steps otherwise.
 * </p>
 */
public class ArraySortInterpretation implements SortInterpretation {
	private final Model mModel;
	private final SortInterpretation mIndexSort;
	private final SortInterpretation mValueSort;

	private final HashMap<Map<Term, Term>, Map<Term, Term>> mUnifier;
	private final HashMap<Term, HashMap<Term, Term>> mDiffMap;

	/**
	 * True if array values are piecewise constant over a numeric index sort. Then every value is normalized by
	 * {@link Piecewise}, and the values that are not store chains are stored in {@link #mPiecewiseValues}.
	 */
	private final boolean mPiecewise;
	private final HashMap<Term, Piecewise> mPiecewiseValues;

	/**
	 * A piecewise-constant array with a numeric index sort. The array has the value {@code mPoints.get(c)} at each
	 * breakpoint {@code c}, the value {@code mAbove.get(c)} between {@code c} and the next breakpoint, and the value
	 * {@code mBelow} below the smallest breakpoint.
	 */
	private static final class Piecewise {
		private final boolean mIsInt;
		private final TreeMap<Rational, Term> mPoints = new TreeMap<>();
		private final TreeMap<Rational, Term> mAbove = new TreeMap<>();
		private final Term mBelow;

		Piecewise(final boolean isInt, final Term below) {
			mIsInt = isInt;
			mBelow = below;
		}

		Piecewise copy() {
			final Piecewise result = new Piecewise(mIsInt, mBelow);
			result.mPoints.putAll(mPoints);
			result.mAbove.putAll(mAbove);
			return result;
		}

		Term get(final Rational index) {
			final Term point = mPoints.get(index);
			if (point != null) {
				return point;
			}
			final Entry<Rational, Term> lower = mAbove.lowerEntry(index);
			return lower == null ? mBelow : lower.getValue();
		}

		/** Add a step: the value from index up to the next breakpoint. */
		void addStep(final Rational index, final Term value) {
			mPoints.put(index, value);
			mAbove.put(index, value);
		}

		void store(final Rational index, final Term value) {
			if (!mPoints.containsKey(index)) {
				mAbove.put(index, get(index));
			}
			mPoints.put(index, value);
		}

		/**
		 * The candidate indices where the value can change, in ascending order: a value below all breakpoints, every
		 * breakpoint, and a value between each breakpoint and the next.
		 */
		List<Rational> getCandidates() {
			final List<Rational> result = new ArrayList<>();
			if (mPoints.isEmpty()) {
				return result;
			}
			result.add(mPoints.firstKey().sub(Rational.ONE));
			for (final Rational point : mPoints.keySet()) {
				result.add(point);
				final Rational next = mPoints.higherKey(point);
				final Rational between = next == null ? point.add(Rational.ONE)
						: mIsInt ? point.add(Rational.ONE) : point.add(next).div(Rational.TWO);
				if (next == null || between.compareTo(next) < 0) {
					result.add(between);
				}
			}
			return result;
		}

		/**
		 * Remove the breakpoints that do not change the value. For Int, the breakpoints are exactly the indices where
		 * the value differs from the value at the index minus one. For Real, the breakpoints are exactly the indices
		 * where the value is not locally constant.
		 */
		void normalize() {
			if (mIsInt) {
				final TreeMap<Rational, Term> steps = new TreeMap<>();
				Term prev = mBelow;
				for (final Rational point : mPoints.keySet()) {
					for (final Rational index : new Rational[] { point, point.add(Rational.ONE) }) {
						final Term value = get(index);
						if (value != prev && !steps.containsKey(index)) {
							steps.put(index, value);
						}
						prev = value;
					}
				}
				mPoints.clear();
				mAbove.clear();
				for (final Entry<Rational, Term> step : steps.entrySet()) {
					addStep(step.getKey(), step.getValue());
				}
			} else {
				Term prev = mBelow;
				for (final Rational point : new ArrayList<>(mPoints.keySet())) {
					if (mPoints.get(point) == prev && mAbove.get(point) == prev) {
						mPoints.remove(point);
						mAbove.remove(point);
					} else {
						prev = mAbove.get(point);
					}
				}
			}
		}

		/** Check if the array differs from its default only at finitely many points. */
		boolean isPointwise() {
			for (final Entry<Rational, Term> above : mAbove.entrySet()) {
				if (above.getValue() == mBelow) {
					continue;
				}
				// for Int, a step back to the default at the next integer
				final Rational next = mPoints.higherKey(above.getKey());
				if (!mIsInt || next == null || !next.equals(above.getKey().add(Rational.ONE))
						|| mPoints.get(next) != mBelow) {
					return false;
				}
			}
			return true;
		}
	}

	public ArraySortInterpretation(final Model model, final SortInterpretation index,
			final SortInterpretation value, final boolean piecewise) {
		mModel = model;
		mIndexSort = index;
		mValueSort = value;
		mUnifier = new HashMap<>();
		final Map<Term, Term> empty = Collections.emptyMap();
		mUnifier.put(empty, empty);
		mDiffMap = new HashMap<>();
		mPiecewise = piecewise;
		mPiecewiseValues = piecewise ? new HashMap<>() : null;
	}

	/**
	 * Create a piecewise-constant array. For a numeric index sort, the array has the value of the greatest step index
	 * below or equal to the index; for other index sorts, it has the value of a step only at its index.
	 *
	 * @param steps
	 *            the step indices and their values.
	 * @param defaultValue
	 *            the value where no step applies.
	 * @param arraySort
	 *            the sort of the array.
	 * @return the normalized array value.
	 */
	public Term createPiecewise(final Map<Term, Term> steps, final Term defaultValue, final Sort arraySort) {
		if (!mPiecewise) {
			return normalizeStoreTerm(createArray(steps, defaultValue, arraySort));
		}
		final Piecewise array = new Piecewise(isIntIndex(arraySort), defaultValue);
		for (final Entry<Term, Term> step : steps.entrySet()) {
			array.addStep(NumericSortInterpretation.toRational(step.getKey()), step.getValue());
		}
		return toTerm(array, arraySort);
	}

	private static boolean isIntIndex(final Sort arraySort) {
		return arraySort.getArguments()[0].getName() == SMTLIBConstants.INT;
	}

	private Piecewise toPiecewise(final Term arrayValue) {
		final Piecewise cached = mPiecewiseValues.get(arrayValue);
		if (cached != null) {
			return cached;
		}
		final ArrayDeque<ApplicationTerm> stores = new ArrayDeque<>();
		ApplicationTerm arrayTerm = (ApplicationTerm) arrayValue;
		while (arrayTerm.getFunction().getName() == SMTLIBConstants.STORE) {
			stores.addFirst(arrayTerm);
			arrayTerm = (ApplicationTerm) arrayTerm.getParameters()[0];
		}
		final Piecewise result;
		if (arrayTerm.getFunction().getName() == SMTLIBConstants.AS_ARRAY) {
			result = mPiecewiseValues.get(arrayTerm).copy();
		} else {
			assert arrayTerm.getFunction().getName() == SMTLIBConstants.CONST;
			result = new Piecewise(isIntIndex(arrayValue.getSort()), arrayTerm.getParameters()[0]);
		}
		for (final ApplicationTerm store : stores) {
			result.store(NumericSortInterpretation.toRational(store.getParameters()[1]), store.getParameters()[2]);
		}
		return result;
	}

	private Term toTerm(final Piecewise array, final Sort arraySort) {
		array.normalize();
		final Theory theory = arraySort.getTheory();
		if (array.isPointwise()) {
			Term result = theory.term(SMTLIBConstants.CONST, null, arraySort, array.mBelow);
			for (final Entry<Rational, Term> point : array.mPoints.entrySet()) {
				if (point.getValue() != array.mBelow) {
					result = theory.term(SMTLIBConstants.STORE, result, point.getKey().toTerm(arraySort.getArguments()[0]),
							point.getValue());
				}
			}
			return result;
		}
		final Sort indexSort = arraySort.getArguments()[0];
		final TermVariable var = theory.createTermVariable("@i", indexSort);
		// first-match ite chain, highest breakpoint first, built from the inside out
		Term body = array.mBelow;
		for (final Entry<Rational, Term> point : array.mPoints.entrySet()) {
			final Rational index = point.getKey();
			if (point.getValue() != body) {
				body = theory.ifthenelse(theory.term(SMTLIBConstants.GEQ, var, index.toTerm(indexSort)),
						point.getValue(), body);
			}
			final Term above = array.mAbove.get(index);
			if (above != point.getValue()) {
				final Term cond = array.mIsInt
						? theory.term(SMTLIBConstants.GEQ, var, index.add(Rational.ONE).toTerm(indexSort))
						: theory.term(SMTLIBConstants.GT, var, index.toTerm(indexSort));
				body = theory.ifthenelse(cond, above, body);
			}
		}
		final Term result = theory.term(SMTLIBConstants.AS_ARRAY, theory.lambda(new TermVariable[] { var }, body));
		mPiecewiseValues.putIfAbsent(result, array);
		return result;
	}

	@Override
	public Term getModelValue(final int idx, final Sort arraySort) {
		final Sort valueSort = arraySort.getArguments()[1];
		return createArray(Collections.emptyMap(), mValueSort.getModelValue(idx, valueSort), arraySort);
	}

	private Term createArray(final Map<Term, Term> mapping, final Term defaultValue, final Sort arraySort) {
		final Theory theory = defaultValue.getTheory();
		final FunctionSymbol constFunc = theory.getFunctionWithResult(SMTLIBConstants.CONST, null, arraySort,
				defaultValue.getSort());
		Term result = theory.term(constFunc, defaultValue);
		final ArrayDeque<Term> keys = new ArrayDeque<>(mapping.keySet());
		// build the store term from back to front
		while (!keys.isEmpty()) {
			final Term index = keys.removeLast();
			result = theory.term("store", result, index, mapping.get(index));
		}
		return result;
	}

	public Term getSelect(final Term storeTerm, final Term selectIndex) {
		if (mPiecewise) {
			return toPiecewise(storeTerm).get(NumericSortInterpretation.toRational(selectIndex));
		}
		ApplicationTerm arrayTerm = (ApplicationTerm) storeTerm;
		while (arrayTerm.getFunction().getName() == "store") {
			if (arrayTerm.getParameters()[1] == selectIndex) {
				return arrayTerm.getParameters()[2];
			}
			arrayTerm = (ApplicationTerm) arrayTerm.getParameters()[0];
		}
		assert arrayTerm.getFunction().getName() == SMTLIBConstants.CONST;
		return arrayTerm.getParameters()[0];
	}

	public Term normalizeStoreTerm(final Term storeTerm) {
		if (mPiecewise) {
			return toTerm(toPiecewise(storeTerm), storeTerm.getSort());
		}
		final Map<Term, Term> map = new LinkedHashMap<>();
		ApplicationTerm arrayTerm = (ApplicationTerm) storeTerm;
		while (arrayTerm.getFunction().getName() == "store") {
			final Term index = arrayTerm.getParameters()[1];
			if (!map.containsKey(index)) {
				map.put(index, arrayTerm.getParameters()[2]);
			}
			arrayTerm = (ApplicationTerm) arrayTerm.getParameters()[0];
		}
		assert arrayTerm.getFunction().getName() == SMTLIBConstants.CONST;
		final Term defaultValue = arrayTerm.getParameters()[0];
		for (final Iterator<Entry<Term, Term>> entryIterator = map.entrySet().iterator(); entryIterator.hasNext();) {
			final Entry<Term, Term> entry = entryIterator.next();
			if (entry.getValue() == defaultValue) {
				entryIterator.remove();
			}
		}
		Map<Term, Term> unified = mUnifier.get(map);
		if (unified == null) {
			mUnifier.put(map, map);
			unified = map;
		}
		return createArray(unified, defaultValue, storeTerm.getSort());
	}

	@Override
	public Term extendFresh(final Sort arraySort) {
		assert arraySort.getSortSymbol().getName() == "Array";
		final Sort indexSort = arraySort.getArguments()[0];
		final Sort valueSort = arraySort.getArguments()[1];
		final Term freshIndex = mIndexSort.extendFresh(indexSort);
		final Term value = mModel.getSecondValue(valueSort);
		final Map<Term, Term> map = Collections.singletonMap(freshIndex, value);
		final Map<Term, Term> old = mUnifier.put(map, map);
		assert old == null;
		return createArray(map, mModel.getSomeValue(valueSort), arraySort);
	}

	@Override
	public Term toSMTLIB(final Theory t, final Sort sort) {
		throw new InternalError("toSMTLIB called");
	}

	public void addDiff(final Term fstArray, final Term sndArray, final Term index) {
		HashMap<Term,Term> subMap = mDiffMap.get(fstArray);
		if (subMap == null) {
			subMap = new HashMap<>();
			mDiffMap.put(fstArray, subMap);
		}
		final Term old = subMap.put(sndArray, index);
		assert old == null || old == index;
	}

	public Term computeDiff(final Term fstArray, final Term sndArray, final Sort indexSort) {
		// first check diff map
		final Map<Term, Term> subMap = mDiffMap.get(fstArray);
		if (subMap != null) {
			final Term result = subMap.get(sndArray);
			if (result != null) {
				return result;
			}
		}

		// return canonical value if arrays equal
		if (fstArray == sndArray) {
			return mModel.getSomeValue(indexSort);
		}

		if (mPiecewise) {
			return computePiecewiseDiff(fstArray, sndArray, indexSort);
		}

		// no diff matches; search first explicit difference

		// first build the map from the second array term.
		final Map<Term, Term> secondValues = new HashMap<>();
		ApplicationTerm arrayTerm = (ApplicationTerm) sndArray;
		while (arrayTerm.getFunction().getName() == "store") {
			final Term index = arrayTerm.getParameters()[1];
			secondValues.put(index, arrayTerm.getParameters()[2]);
			arrayTerm = (ApplicationTerm) arrayTerm.getParameters()[0];
		}
		assert arrayTerm.getFunction().getName() == SMTLIBConstants.CONST;
		final Term secondDefault = arrayTerm.getParameters()[0];

		// check each entry in the first array term, whether it differs.
		arrayTerm = (ApplicationTerm) fstArray;
		while (arrayTerm.getFunction().getName() == "store") {
			final Term index = arrayTerm.getParameters()[1];
			Term secondValue = secondValues.get(index);
			if (secondValue == null) {
				secondValue = secondDefault;
			}
			// check if firstValue is defined there and differs.
			if (secondValue != arrayTerm.getParameters()[2]) {
				return index;
			}
			arrayTerm = (ApplicationTerm) arrayTerm.getParameters()[0];
		}
		assert arrayTerm.getFunction().getName() == SMTLIBConstants.CONST;
		// they must differ on default value, so just return a fresh value.
		assert secondDefault != arrayTerm.getParameters()[0];
		final Term diffIndex = mIndexSort.extendFresh(indexSort);
		// store the index for future use, so we will return it again.
		addDiff(fstArray, sndArray, diffIndex);
		return diffIndex;
	}

	private Term computePiecewiseDiff(final Term fstArray, final Term sndArray, final Sort indexSort) {
		final Piecewise fst = toPiecewise(fstArray);
		final Piecewise snd = toPiecewise(sndArray);
		final TreeSet<Rational> candidates = new TreeSet<>(fst.getCandidates());
		candidates.addAll(snd.getCandidates());
		for (final Rational index : candidates) {
			if (fst.get(index) != snd.get(index)) {
				return index.toTerm(indexSort);
			}
		}
		// the arrays differ only below every breakpoint, or have no breakpoints
		assert fst.mBelow != snd.mBelow;
		final Rational below = candidates.isEmpty() ? Rational.ZERO : candidates.first().sub(Rational.ONE);
		return below.toTerm(indexSort);
	}

	public SortInterpretation getIndexInterpretation() {
		return mIndexSort;
	}

	public SortInterpretation getValueInterpretation() {
		return mValueSort;
	}

	@Override
	public void register(final Term t) {
	}
}
