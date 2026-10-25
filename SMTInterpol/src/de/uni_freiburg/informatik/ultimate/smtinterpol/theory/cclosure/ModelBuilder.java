/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.ArraySortInterpretation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.BitVectorInterpretation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.FunctionValue;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.NumericSortInterpretation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ComputeSCC;

public class ModelBuilder {

	/**
	 * What the quantifier theory's model-based final check assumed about the model (see
	 * {@code doc/piecewise-constant-models.md}, Step 4). With quantified clauses the uninterpreted functions get the
	 * piecewise-constant model of {@link PiecewiseModel}, the CC-only numeric classes get values far enough apart that
	 * the signs the final check derived for sums over them stay true, and lambda gets a value below all of them.
	 */
	public static final class QuantifierInfo {
		final Function<Sort, CCTerm> mLambdaTerms;
		final List<CCParameter> mUseSites;
		final Rational mCoeffSum;
		final Rational mConstant;
		final Rational mDenominator;
		final Rational mMaxGroundValue;

		/**
		 * @param lambdaTerms
		 *            maps a sort to the CCTerm of its lambda, or to null if it has none.
		 * @param useSites
		 *            the values the quantified literals compare variables with, including their offsets {@code ±1}.
		 * @param coeffSum
		 *            an upper bound for the sum of the absolute coefficients of every sum the final check evaluates.
		 * @param constant
		 *            an upper bound for the absolute constant of every such sum.
		 * @param denominator
		 *            a common denominator of all coefficients, so every non-zero sum of coefficients is at least
		 *            {@code 1/denominator} in absolute value.
		 * @param maxGroundValue
		 *            an upper bound for the absolute value of ground terms in the quantified literals that are neither
		 *            in the congruence closure nor in {@code constant}.
		 */
		public QuantifierInfo(final Function<Sort, CCTerm> lambdaTerms, final List<CCParameter> useSites,
				final Rational coeffSum, final Rational constant, final Rational denominator,
				final Rational maxGroundValue) {
			mLambdaTerms = lambdaTerms;
			mUseSites = useSites;
			mCoeffSum = coeffSum;
			mConstant = constant;
			mDenominator = denominator;
			mMaxGroundValue = maxGroundValue;
		}

		/**
		 * The distance a value must keep from every other value so that the sign of a sum in which it occurs with a
		 * non-zero coefficient is the sign of that coefficient: {@code (K·M + C + 1)·D + M}, rounded up.
		 *
		 * @param maxValue
		 *            an upper bound {@code M} for the absolute values of the other values in the sum.
		 */
		Rational getGap(final Rational maxValue) {
			return mCoeffSum.mul(maxValue).add(mConstant).add(Rational.ONE).mul(mDenominator).ceil().add(maxValue);
		}
	}


	Model mModel;
	SharedTermEvaluator mEvaluator;
	Map<CCTerm, Term> mModelValues = new HashMap<>();
	Theory mTheory;
	/**
	 * For each representative of a numeric congruence class, the minimal/maximal offset at which any use site (a class
	 * member or a function application argument) references the class. The value at such a use site is the
	 * representative's value plus the offset, so a freshly chosen class value must keep the whole range
	 * {@code [value+min, value+max]} clear of other model values, not just the value itself.
	 */
	Map<CCTerm, Rational> mMinOffset = new HashMap<>();
	Map<CCTerm, Rational> mMaxOffset = new HashMap<>();

	/** The quantifier information, or null if there are no quantified clauses. */
	final QuantifierInfo mQuantInfo;
	/** The piecewise-constant model of the uninterpreted functions, if there are quantified clauses. */
	PiecewiseModel mPiecewiseModel;
	/** The numeric classes without shared term, in the order of {@code terms}; only with quantified clauses. */
	final List<CCTerm> mDelayedNumeric = new ArrayList<>();
	/** The model value of lambda per sort, i.e., of every argument not covered by a corner. */
	final Map<Sort, Term> mLambdaValues = new HashMap<>();
	/** The model value of lambda of the numeric sorts. */
	Rational mNumericLambda;

	public ModelBuilder(final CClosure closure, final List<CCTerm> terms, final Model model,
			final Theory t, final SharedTermEvaluator ste,
			final ArrayTheory arrayTheory, final DataTypeTheory datatypeTheory, final CCTerm trueNode,
			final CCTerm falseNode, final QuantifierInfo quantInfo) {
		mModel = model;
		mEvaluator = ste;
		mTheory = t;
		mQuantInfo = quantInfo;

		// collect the offset range at which each numeric class is used: every member and every function application
		// argument is a use site whose model value is the representative's value plus its offset to the representative.
		for (final CCTerm term : terms) {
			final Term flatTerm = term.getFlatTerm();
			if (flatTerm != null && flatTerm.getSort().isNumericSort()) {
				updateOffsetRange(term.getRepresentative(), term.getOffsetToRep());
			}
			if (term instanceof CCAppTerm) {
				final CCAppTerm app = (CCAppTerm) term;
				for (int i = 0; i < app.getArgCount(); i++) {
					final CCParameter arg = app.getArgParam(i);
					final Term argTerm = arg.getCCTerm().getFlatTerm();
					if (argTerm != null && argTerm.getSort().isNumericSort()) {
						updateOffsetRange(arg.getRepresentative(), arg.getOffsetToRep());
					}
				}
			}
		}
		if (quantInfo != null) {
			// the values the quantified literals compare with are use sites too, so no fresh value lands in between
			for (final CCParameter useSite : quantInfo.mUseSites) {
				updateOffsetRange(useSite.getRepresentative(), useSite.getOffsetToRep());
			}
		}

		// create a map from sorts to representatives of that sort.
		final LinkedHashMap<Sort, List<CCTerm>> repsBySort = new LinkedHashMap<>();
		for (final CCTerm term : terms) {
			if (term.getRepresentative() == term && term.getFlatTerm() != null) {
				final Sort sort = term.getFlatTerm().getSort();
				List<CCTerm> reps = repsBySort.get(sort);
				if (reps == null) {
					reps = new ArrayList<>();
					repsBySort.put(sort, reps);
				}
				reps.add(term);
			}
		}

		// We need a topological ordering on the sorts.
		final ComputeSCC.ComputeSuccessor<Sort> dependencies = (final Sort sort) ->  {
			if (sort.isArraySort()) {
				return Arrays.asList(sort.getArguments()).iterator();
			} else if (sort.getSortSymbol().isDatatype()) {
				final Sort[] datatypeParameters = sort.getArguments();
				final Constructor[] constrs = ((DataType) sort.getSortSymbol()).getConstructors();
				return new Iterator<Sort>() {
					int mConstructorIdx = 0;
					int mSortIdx = 0;
					// datatypes always depend on Bool for tester
					Sort[] mSorts = new Sort[] { t.getBooleanSort() };

					@Override
					public boolean hasNext() {
						while (mSortIdx >= mSorts.length) {
							if (mConstructorIdx == constrs.length) {
								return false;
							}
							mSorts = constrs[mConstructorIdx++].getArgumentSorts();
							mSortIdx = 0;
						}
						return true;
					}

					@Override
					public Sort next() {
						while (mSortIdx >= mSorts.length) {
							mSorts = constrs[mConstructorIdx++].getArgumentSorts();
							mSortIdx = 0;
						}
						final Sort dependentSort = mSorts[mSortIdx++];
						return datatypeParameters == null ? dependentSort : dependentSort.mapSort(datatypeParameters);
					}
				};
			} else if (sort.isBitVecSort()) {
				return Collections.singleton(sort.getTheory().getNumericSort()).iterator();
			} else {
				return Collections.emptyListIterator();
			}
		};
		final List<List<Sort>> sortSCCs = new ComputeSCC<>(dependencies).getSCCs(repsBySort.keySet().iterator());

		if (quantInfo != null) {
			// The CC-only classes of all numeric sorts are ordered together (as in PiecewiseModel) and lambda must be
			// below all of them, so the numeric sorts, which depend on no other sort, are filled in first.
			for (final Map.Entry<Sort, List<CCTerm>> entry : repsBySort.entrySet()) {
				if (entry.getKey().isNumericSort()) {
					fillInTermValues(entry.getValue(), trueNode, falseNode);
				}
			}
			fillInDelayedNumeric(terms);
			mPiecewiseModel = new PiecewiseModel(closure, arrayTheory, ste, quantInfo.mLambdaTerms);
		}
		for (final List<Sort> scc : sortSCCs) {
			if (quantInfo != null && scc.get(0).isNumericSort()) {
				continue;
			}
			if (scc.get(0).getSortSymbol().isDatatype()) {
				datatypeTheory.fillInModel(this, scc, repsBySort);
			} else {
				assert scc.size() == 1;
				final Sort sort = scc.get(0);
				if (repsBySort.containsKey(sort)) {
					if (sort.isArraySort()) {
						if (quantInfo != null && arrayTheory.isNeedDiffIndices()) {
							fillInPiecewiseArrays(repsBySort.get(sort));
						} else {
							// without quantified indices, the final check only selects at ground indices
							arrayTheory.fillInModel(this, repsBySort.get(sort));
						}
					} else {
						fillInTermValues(repsBySort.get(sort), trueNode, falseNode);
					}
				}
			}
		}
		fillInFunctions(terms, model, t);
	}

	public Model getModel() {
		return mModel;
	}

	public Theory getTheory() {
		return mTheory;
	}

	public SharedTermEvaluator getEvaluator() {
		return mEvaluator;
	}

	/**
	 * The model value of a {@link CCParameter} value {@code term + offset}: the representative's model value shifted by
	 * the parameter's offset to the representative. A bare {@link CCTerm} is an offset-free parameter, so this returns
	 * its representative's value; a numeric member additionally adds its offset to the representative. Returns
	 * {@code null} if the class has no model value yet (used as a "value computed?" check) &mdash; this only happens for
	 * non-numeric sorts, where no offset arithmetic is attempted on the missing value.
	 *
	 * <p>This is the only model-value accessor: there is deliberately no {@code getModelValue(CCTerm)}, since looking up
	 * a bare representative would silently drop a member's offset (returning the representative's value instead of the
	 * member's) &mdash; a subtle source of wrong models for numeric terms.
	 */
	public Term getModelValue(final CCParameter param) {
		final Term repValue = mModelValues.get(param.getRepresentative());
		final Sort sort = param.getCCTerm().getFlatTerm().getSort();
		if (!sort.isNumericSort()) {
			assert param.getOffsetToRep().equals(Rational.ZERO);
			return repValue;
		}
		// the member's value is the representative's value shifted by the parameter's offset to the representative
		// (which folds in both the class offset and the structural argument offset, e.g. the +5 in x+5).
		return NumericSortInterpretation.toRational(repValue).add(param.getOffsetToRep()).toTerm(sort);
	}

	private void updateOffsetRange(final CCTerm rep, final Rational offset) {
		final Rational min = mMinOffset.get(rep);
		if (min == null || offset.compareTo(min) < 0) {
			mMinOffset.put(rep, offset);
		}
		final Rational max = mMaxOffset.get(rep);
		if (max == null || offset.compareTo(max) > 0) {
			mMaxOffset.put(rep, offset);
		}
	}

	public void setModelValue(final CCTerm term, final Term value) {
		assert term == term.getRepresentative();
		final Term old = mModelValues.put(term, value);
		mModel.provideSortInterpretation(value.getSort()).register(value);
		if (value.getSort().isNumericSort()) {
			// mark the largest use-site value of the class as used, so fresh values avoid the whole class range.
			final Rational maxOffset = mMaxOffset.get(term);
			if (maxOffset != null && maxOffset.signum() > 0) {
				mModel.provideSortInterpretation(value.getSort())
						.register(NumericSortInterpretation.toRational(value).add(maxOffset).toTerm(value.getSort()));
			}
		}
		assert old == null || old == value;
	}

	public void fillInTermValues(final List<CCTerm> terms, final CCTerm trueNode, final CCTerm falseNode) {
		final List<CCTerm> delayed = new ArrayList<>();
		for (final CCTerm ccterm : terms) {
			if (ccterm == ccterm.mRepStar) {
				Term value;
				final Term smtterm = ccterm.getFlatTerm();
				final Sort sort = smtterm.getSort();
				if (sort.isNumericSort()) {
					Rational v;
					if (ccterm.getSharedTerm() != null) {
						final CCTerm shared = ccterm.getSharedTerm();
						// evaluate gives the value of the (offset-free) shared term; the representative's value is that
						// minus the shared term's offset to the representative.
						v = mEvaluator.evaluate(shared.getFlatTerm(), mTheory).sub(shared.getOffsetToRep());
						if (smtterm.getSort().getName().equals("Int") && !v.isIntegral()) {
							throw new AssertionError("Int term has non-integral value");
						}
						value = v.toTerm(sort);
					} else {
						delayed.add(ccterm);
						continue;
					}
				} else if (ccterm.getFlatTerm().getSort().isBitVecSort()) {
					value = null;
					for (final CCTerm member : ccterm.mRepStar.mMembers) {
						final Term t = member.getFlatTerm();
						if (t instanceof ApplicationTerm) {
							if (((ApplicationTerm) t).getFunction().getName().equals(SMTLIBConstants.INT_TO_BV)) {
								final Term arg = ((ApplicationTerm) t).getParameters()[0];
								final Rational v = mEvaluator.evaluate(arg, mTheory);
								assert v.isIntegral();
								BigInteger vInt = v.numerator();
								final int width = Integer.parseInt(t.getSort().getIndices()[0]);
								vInt = vInt.mod(BigInteger.ONE.shiftLeft(width));
								value = BitVectorInterpretation.BV(vInt, t.getSort());
								break;
							}
						}
					}
					assert value != null;
				} else if (ccterm == trueNode.mRepStar) {
					value = sort.getTheory().mTrue;
				} else if (sort.isInternal() && sort.getName().equals(SMTLIBConstants.BOOL)) {
					// By convention, we convert to == TRUE.  Hence, if a value
					// is not equal to TRUE but Boolean, we have to adjust the
					// model and set it to false.
					value = sort.getTheory().mFalse;
				} else {
					assert !sort.isArraySort() && !sort.getSortSymbol().isDatatype();
					value = mModel.extendFresh(sort);
				}
				setModelValue(ccterm, value);
			}
		}
		if (mQuantInfo != null) {
			mDelayedNumeric.addAll(delayed);
			return;
		}
		// Handle all delayed elements
		// note that extendFresh must be called after all values in the model have been extended to the numeric sort.
		for (final CCTerm ccterm : delayed) {
			final Sort sort = ccterm.getFlatTerm().getSort();
			Rational value = NumericSortInterpretation.toRational(mModel.extendFresh(sort));
			// shift by the class's smallest use-site offset, so even the smallest use-site value (value + minOffset)
			// is the fresh one; setModelValue then marks the largest one (value + maxOffset) as used.
			final Rational minOffset = mMinOffset.get(ccterm);
			if (minOffset != null && minOffset.signum() < 0) {
				value = value.sub(minOffset);
			}
			setModelValue(ccterm, value.toTerm(sort));
		}
	}

	/**
	 * Give the numeric classes without shared term their values, if there are quantified clauses. The final check
	 * treated them symbolically: every such class is above all concrete values, the later class (in the order of
	 * {@code terms}) is above the earlier plus any offset, and lambda is below everything, also when multiplied by a
	 * coefficient and added to the other values of a sum. So the classes get values in that order, each at least
	 * {@link QuantifierInfo#getGap} above all values so far, and lambda gets a value that far below all values.
	 */
	private void fillInDelayedNumeric(final List<CCTerm> terms) {
		final Map<CCTerm, Integer> order = new HashMap<>();
		for (final CCTerm term : terms) {
			if (term.isRepresentative()) {
				order.put(term, order.size());
			}
		}
		mDelayedNumeric.sort((t1, t2) -> Integer.compare(order.get(t1), order.get(t2)));
		final List<CCTerm> lambdas = new ArrayList<>();
		final Rational gap = mQuantInfo.getGap(getMaxAbsNumericValue());
		for (final CCTerm ccterm : mDelayedNumeric) {
			final Sort sort = ccterm.getFlatTerm().getSort();
			final CCTerm lambda = mQuantInfo.mLambdaTerms.apply(sort);
			if (lambda != null && lambda.getRepresentative() == ccterm && PiecewiseModel.isSymbolicLambda(ccterm)) {
				lambdas.add(ccterm);
				continue;
			}
			// the class's smallest use site keeps the gap to everything below
			Rational value = NumericSortInterpretation.toRational(mModel.extendFresh(sort)).add(gap);
			final Rational minOffset = mMinOffset.get(ccterm);
			if (minOffset != null && minOffset.signum() < 0) {
				value = value.sub(minOffset);
			}
			setModelValue(ccterm, value.toTerm(sort));
		}
		// lambda goes below everything, including the CC-only values just assigned
		final Rational maxValue = getMaxAbsNumericValue();
		final Rational lambdaValue = mQuantInfo.getGap(maxValue).add(maxValue).negate();
		for (final CCTerm lambda : lambdas) {
			final Rational maxOffset = mMaxOffset.get(lambda);
			final Rational value = maxOffset != null && maxOffset.signum() > 0 ? lambdaValue.sub(maxOffset)
					: lambdaValue;
			setModelValue(lambda, value.toTerm(lambda.getFlatTerm().getSort()));
		}
		mNumericLambda = lambdaValue;
	}

	/**
	 * An upper bound for the absolute value of every numeric model value assigned so far, including the offsets of
	 * the use sites, and of the ground values and constants of the quantified literals.
	 */
	private Rational getMaxAbsNumericValue() {
		Rational max = Rational.ONE;
		max = maxAbs(max, mQuantInfo.mMaxGroundValue);
		max = maxAbs(max, mQuantInfo.mConstant);
		for (final Map.Entry<CCTerm, Rational> entry : mMinOffset.entrySet()) {
			final CCTerm rep = entry.getKey();
			final Rational minOffset = entry.getValue();
			final Rational maxOffset = mMaxOffset.get(rep);
			final Term value = mModelValues.get(rep);
			final Rational base = value == null ? Rational.ZERO : NumericSortInterpretation.toRational(value);
			max = maxAbs(max, base.add(minOffset));
			max = maxAbs(max, base.add(maxOffset));
			max = maxAbs(max, minOffset);
			max = maxAbs(max, maxOffset);
		}
		for (final Map.Entry<CCTerm, Term> entry : mModelValues.entrySet()) {
			if (entry.getValue().getSort().isNumericSort()) {
				max = maxAbs(max, NumericSortInterpretation.toRational(entry.getValue()));
			}
		}
		return max;
	}

	private static Rational maxAbs(final Rational max, final Rational value) {
		return value.abs().compareTo(max) > 0 ? value.abs() : max;
	}

	/**
	 * The model value of lambda of a sort, i.e., the value of a function where no corner covers its arguments. For
	 * numeric sorts it is below everything, for other sorts it is the value of the symbolic lambda class or a fresh
	 * value, so that it differs from every class.
	 */
	private Term getLambdaValue(final Sort sort) {
		Term value = mLambdaValues.get(sort);
		if (value != null) {
			return value;
		}
		if (sort.isNumericSort()) {
			value = mNumericLambda.toTerm(sort);
		} else if (sort == mTheory.getBooleanSort()) {
			// the final check compares a predicate's value with true, so lambda is false
			value = mTheory.mFalse;
		} else if (sort.isArraySort() || sort.getSortSymbol().isDatatype() || sort.isBitVecSort()
				|| sort.isInternal()) {
			// TODO: the final check does not decide anything on such lambda values
			value = mModel.getSomeValue(sort);
		} else {
			final CCTerm lambda = mQuantInfo.mLambdaTerms.apply(sort);
			if (lambda != null && PiecewiseModel.isSymbolicLambda(lambda.getRepresentative())) {
				value = getModelValue(lambda);
			} else {
				value = mModel.extendFresh(sort);
			}
		}
		mLambdaValues.put(sort, value);
		return value;
	}

	/**
	 * Fill in the piecewise-constant models of the arrays (see {@link PiecewiseModel#evaluateSelect}): the steps of the
	 * weak representative at its selects, and the stores on top.
	 */
	private void fillInPiecewiseArrays(final List<CCTerm> arrays) {
		final Sort arraySort = arrays.get(0).getFlatTerm().getSort();
		final Sort elemSort = arraySort.getArguments()[1];
		final ArraySortInterpretation interpretation =
				(ArraySortInterpretation) mModel.provideSortInterpretation(arraySort);
		for (final CCTerm array : arrays) {
			final PiecewiseModel.ArrayModel arrayModel = mPiecewiseModel.getArrayModel(array);
			Term defaultValue =
					arrayModel.mDefault == null ? getLambdaValue(elemSort) : getModelValue(arrayModel.mDefault);
			final Map<Term, Term> steps = new LinkedHashMap<>();
			for (final CCAppTerm select : arrayModel.mCorners) {
				final CCParameter index = ArrayTheory.getIndexFromSelect(select);
				final Term value = getModelValue(select.getValueKey());
				if (mPiecewiseModel.getValue(index).isLambda()) {
					// lambda is below every index, so the select covers every index without another step
					defaultValue = value;
				} else {
					steps.put(getModelValue(index), value);
				}
			}
			Term arrayValue = interpretation.createPiecewise(steps, defaultValue, arraySort);
			for (int i = 0; i < arrayModel.mStoreIndices.size(); i++) {
				final CCAppTerm select = arrayModel.mStoreValues.get(i);
				final Term value = select == null ? getLambdaValue(elemSort) : getModelValue(select.getValueKey());
				arrayValue = interpretation.normalizeStoreTerm(mTheory.term(SMTLIBConstants.STORE, arrayValue,
						getModelValue(arrayModel.mStoreIndices.get(i)), value));
			}
			setModelValue(array, arrayValue);
		}
	}

	public void fillInFunctions(final List<CCTerm> terms, final Model model, final Theory t) {
		for (final CCTerm term : terms) {
			if (mQuantInfo != null && term instanceof CCAppTerm
					&& !((CCAppTerm) term).getFunctionSymbol().isIntern()) {
				// uninterpreted functions get their piecewise-constant model below
				continue;
			}
			add(model, term, getModelValue(term), t);
		}
		if (mQuantInfo != null) {
			for (final FunctionSymbol fs : t.getDeclaredFunctions().values()) {
				if (!fs.isIntern() && fs.getDefinition() == null && fs.getParameterSorts().length > 0) {
					addPiecewiseFunction(model, fs);
				}
			}
		}
	}

	/**
	 * Add the piecewise-constant model of an uninterpreted function: its corners in the order {@link PiecewiseModel}
	 * searches them, and lambda of the return sort where no corner covers the arguments. A coordinate that is lambda
	 * covers every argument, so lambda acts like minus infinity in argument positions.
	 */
	private void addPiecewiseFunction(final Model model, final FunctionSymbol fs) {
		final FunctionValue value = model.mapPiecewise(fs, getLambdaValue(fs.getReturnSort()));
		for (final CCAppTerm corner : mPiecewiseModel.getCorners(fs)) {
			final Term[] coordinates = new Term[corner.getArgCount()];
			for (int i = 0; i < coordinates.length; i++) {
				final CCParameter arg = corner.getArgParam(i);
				coordinates[i] = mPiecewiseModel.getValue(arg).isLambda() ? null : getModelValue(arg);
			}
			value.addStep(coordinates, getModelValue(corner));
		}
	}

	private void add(final Model model, final CCTerm term, final Term value, final Theory t) {
		if (term instanceof CCBaseTerm) {
			final CCBaseTerm bt = (CCBaseTerm) term;
			final Term btTerm = bt.getFlatTerm();
			if (btTerm instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) btTerm;
				final FunctionSymbol symb = appTerm.getFunction();
				if (!symb.isIntern() && appTerm.getParameters().length == 0) {
					model.map(symb, value);
				}
			}
		} else {
			// It is a CCAppTerm
			final CCAppTerm app = (CCAppTerm) term;
			addApp(model, app, value, t);
		}
	}

	private static boolean isDivision(final FunctionSymbol fs) {
		final String name = fs.getName();
		return name == "/" || name == "div" || name == "mod";
	}

	private boolean isUndefinedFor(FunctionSymbol fs, Term[] args) {
		if (fs.isSelector()) {
			final DataType datatype = (DataType) fs.getParameterSorts()[0].getSortSymbol();
			final ApplicationTerm arg = (ApplicationTerm) args[0];
			final Constructor c = datatype.getConstructor(arg.getFunction().getName());
			// A selector is undefined if the argument's constructor doesn't match
			return !Arrays.asList(c.getSelectors()).contains(fs.getName());
		} else if (isDivision(fs)) {
			// A division by zero is undefined
			return NumericSortInterpretation.toRational(args[1]) == Rational.ZERO;
		} else if (fs.getName() == Interpolator.EQ) {
			return true;
		}
		return false;
	}

	private void addApp(final Model model, final CCAppTerm app, final Term value, final Theory t) {
		Term[] args = new Term[app.getArgCount()];
		for (int i = 0; i < args.length; i++) {
			// the actual argument is the CCParameter's term + offset, evaluated at its model value
			final CCParameter argParam = app.getArgParam(i);
			args[i] = getModelValue(argParam);
		}
		final FunctionSymbol fs = app.getFunctionSymbol();
		if (!fs.isIntern() || isUndefinedFor(fs, args)) {
			model.map(fs, args, value);
		} else if (fs.getName() == SMTInterpolConstants.DIFF) {
			final ArraySortInterpretation arraySort = (ArraySortInterpretation) model
					.provideSortInterpretation(fs.getParameterSorts()[0]);
			assert args.length == 2;
			arraySort.addDiff(args[0], args[1], value);
		}
	}

}
