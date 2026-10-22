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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class FunctionValue {

	public static class Index {
		private final Term[] mIdx;
		private final int mHash;

		public Index(final Term[] idx) {
			mIdx = idx;
			mHash = Arrays.hashCode(mIdx);
		}

		@Override
		public int hashCode() {
			return mHash;
		}

		@Override
		public boolean equals(final Object o) {
			if (o instanceof Index) {
				return Arrays.equals(mIdx, ((Index) o).mIdx);
			}
			return false;
		}

		public Term[] toArray() {
			return mIdx;
		}

		@Override
		public String toString() {
			return Arrays.toString(mIdx);
		}
	}

	/**
	 * A step of a piecewise-constant function: the value at every argument tuple covered by the coordinates. A numeric
	 * coordinate {@code c} covers the arguments {@code >= c}, another coordinate covers only itself, and a null
	 * coordinate covers every argument.
	 */
	public static class Step {
		private final Term[] mCoordinates;
		private final Term mValue;

		Step(final Term[] coordinates, final Term value) {
			mCoordinates = coordinates;
			mValue = value;
		}

		public Term[] getCoordinates() {
			return mCoordinates;
		}

		public Term getValue() {
			return mValue;
		}

		boolean covers(final Term[] args) {
			for (int i = 0; i < args.length; i++) {
				final Term coord = mCoordinates[i];
				if (coord == null) {
					continue;
				}
				if (coord.getSort().isNumericSort()) {
					if (NumericSortInterpretation.toRational(args[i])
							.compareTo(NumericSortInterpretation.toRational(coord)) < 0) {
						return false;
					}
				} else if (args[i] != coord) {
					return false;
				}
			}
			return true;
		}

		Term generateCondition(final Term[] vars) {
			final Theory theory = mValue.getTheory();
			final ArrayList<Term> conj = new ArrayList<>();
			for (int i = 0; i < vars.length; i++) {
				final Term coord = mCoordinates[i];
				if (coord != null) {
					conj.add(theory.term(coord.getSort().isNumericSort() ? SMTLIBConstants.GEQ : SMTLIBConstants.EQUALS,
							vars[i], coord));
				}
			}
			return conj.isEmpty() ? theory.mTrue : theory.and(conj.toArray(new Term[conj.size()]));
		}
	}

	private final FunctionSymbol mFunc;
	private Map<Index, Term> mValues;
	/**
	 * The steps of a piecewise-constant function, or null for a function given by its values at single points. The
	 * value at some arguments is the value of the first step covering them, or the default if there is none.
	 */
	private List<Step> mSteps;

	private Term mDefault;

	private LambdaTerm mDefinition;

	public FunctionValue(FunctionSymbol fs, final Term defaultValue) {
		mFunc = fs;
		mDefault = defaultValue;
	}

	public void put(final Term value, final Term... idx) {
		if (idx.length == 0) {
			assert mDefault == null;
			mDefault = value;
		} else {
			if (mValues == null) {
				mValues = new HashMap<>();
			}
			mValues.put(new Index(idx), value);
		}
	}

	/**
	 * Add a step to a piecewise-constant function. Steps are searched in the order they are added.
	 *
	 * @param coordinates
	 *            the coordinates of the step; null for a coordinate that covers every argument.
	 * @param value
	 *            the value of the function on the step.
	 */
	public void addStep(final Term[] coordinates, final Term value) {
		assert mValues == null && coordinates.length == mFunc.getParameterSorts().length;
		if (mSteps == null) {
			mSteps = new ArrayList<>();
		}
		mSteps.add(new Step(coordinates, value));
	}

	public List<Step> getSteps() {
		return mSteps != null ? mSteps : Collections.emptyList();
	}

	public Term get(final Term[] idx) {
		if (mSteps != null) {
			for (final Step step : mSteps) {
				if (step.covers(idx)) {
					return step.getValue();
				}
			}
			return mDefault;
		}
		if (mValues == null) {
			return mDefault;
		}
		final Term res = mValues.get(new Index(idx));
		return res == null ? mDefault : res;
	}

	Term generateCondition(final Index index, final Term[] vars) {
		final Theory theory = mDefault.getTheory();
		final Term[] idx = index.toArray();
		assert vars.length == idx.length;
		final Term[] conj = new Term[vars.length];
		for (int i = 0; i < vars.length; ++i) {
			conj[i] = theory.term(SMTLIBConstants.EQUALS, vars[i], idx[i]);
		}
		return theory.and(conj);
	}

	private static boolean isDivision(final FunctionSymbol fs) {
		final String name = fs.getName();
		return fs.isIntern() && (name == "/" || name == "div" || name == "mod");
	}

	public LambdaTerm getDefinition() {
		if (mDefinition != null) {
			return mDefinition;
		}
		final Theory theory = mFunc.getTheory();
		final Sort[] paramSorts = mFunc.getParameterSorts();
		final TermVariable[] vars = new TermVariable[paramSorts.length];
		for (int i = 0; i < vars.length; ++i) {
			vars[i] = theory.createTermVariable("@p" + i, paramSorts[i]);
		}
		final Term defaultVal = getDefault();
		Term definition = defaultVal;
		for (int i = getSteps().size() - 1; i >= 0; i--) {
			final Step step = mSteps.get(i);
			final Term cond = step.generateCondition(vars);
			definition = cond == theory.mTrue ? step.getValue()
					: step.getValue() == definition ? definition : theory.ifthenelse(cond, step.getValue(), definition);
		}
		for (final Entry<Index, Term> me : values().entrySet()) {
			if (me.getValue() != defaultVal) {
				final Term cond = generateCondition(me.getKey(), vars);
				definition = theory.ifthenelse(cond, me.getValue(), definition);
			}
		}
		if (mFunc.isSelector()) {
			assert vars.length == 1;
			final Sort sort = mFunc.getParameterSorts()[0];
			final DataType datatype = (DataType) sort.getSortSymbol();
			Constructor constr = null;
			for (final Constructor c : datatype.getConstructors()) {
				if (Arrays.asList(c.getSelectors()).contains(mFunc.getName())) {
					constr = c;
				}
			}
			final Term tester = theory.term(SMTLIBConstants.IS, new String[] { constr.getName() }, null, vars[0]);
			definition = theory.ifthenelse(tester, theory.term(mFunc, vars[0]), definition);
		}
		if (isDivision(mFunc)) {
			final Term isZero = theory.term(SMTLIBConstants.EQUALS, vars[1], Rational.ZERO.toTerm(vars[1].getSort()));
			definition = theory.ifthenelse(theory.term(SMTLIBConstants.NOT, isZero),
					theory.term(mFunc, vars[0], vars[1]), definition);
		}
		mDefinition = (LambdaTerm) theory.lambda(vars, definition);
		return mDefinition;
	}

	public Term getDefault() {
		return mDefault;
	}

	public Map<Index, Term> values() {
		return mValues != null ? mValues : Collections.emptyMap();
	}
}
