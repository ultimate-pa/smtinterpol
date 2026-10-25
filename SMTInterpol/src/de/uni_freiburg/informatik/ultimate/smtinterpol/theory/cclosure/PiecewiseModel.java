/*
 * Copyright (C) 2026 University of Freiburg
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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;

/**
 * A symbolic piecewise-constant model of the uninterpreted functions, built from the congruence closure after the
 * final check (see {@code doc/piecewise-constant-models.md}).
 *
 * <p>
 * The model of {@code f} is determined by its <em>corners</em>, the ground applications {@code f(c1,...,cn)} in the
 * E-graph. An argument tuple {@code (a1,...,an)} gets the value of the lexicographically greatest corner {@code c}
 * with {@code ci <= ai} for every numeric position and {@code ci ~ ai} or {@code ci = lambda} for every other position.
 * If no such corner exists, the value is lambda of the return sort. Arrays are modelled the same way, with the
 * selects as corners, but only for the weak representatives; the other arrays add their stores on top (see
 * {@link #evaluateSelect}).
 * </p>
 *
 * <p>
 * Values are symbolic (see {@link Value}): a numeric value is lambda (below everything), a concrete rational (the class
 * has an LA shared term), or a CC-only value {@code rep + offset} (above all concrete values, ordered by class creation
 * order, then offset). Concrete values are only fixed when the model is printed. The model is a snapshot: it must be
 * rebuilt after the congruence closure changed.
 * </p>
 *
 * @author Jochen Hoenicke
 */
public class PiecewiseModel {

	/**
	 * A symbolic model value. Numeric values are totally ordered: lambda, then concrete values by value, then CC-only
	 * values by class order and offset. Values of other sorts are congruence classes (or lambda) without an order.
	 */
	public static final class Value implements Comparable<Value> {
		private enum Kind {
			LAMBDA, CONCRETE, CC_ONLY, CLASS
		}

		private final Sort mSort;
		private final Kind mKind;
		/** The concrete value for {@code CONCRETE}, the offset to the representative for {@code CC_ONLY}. */
		private final Rational mRational;
		/** The representative for {@code CC_ONLY} and {@code CLASS}. */
		private final CCTerm mRep;
		/** The creation index of the representative for {@code CC_ONLY}, i.e., the class order. */
		private final int mOrder;

		private Value(final Sort sort, final Kind kind, final Rational rational, final CCTerm rep, final int order) {
			mSort = sort;
			mKind = kind;
			mRational = rational;
			mRep = rep;
			mOrder = order;
		}

		/** The lambda value of the given sort, the value of all arguments not covered by a corner. */
		public static Value lambda(final Sort sort) {
			return new Value(sort, Kind.LAMBDA, null, null, 0);
		}

		/** A concrete numeric value. */
		public static Value concrete(final Sort sort, final Rational value) {
			assert sort.isNumericSort();
			return new Value(sort, Kind.CONCRETE, value, null, 0);
		}

		public Sort getSort() {
			return mSort;
		}

		public boolean isLambda() {
			return mKind == Kind.LAMBDA;
		}

		public boolean isConcrete() {
			return mKind == Kind.CONCRETE;
		}

		/** The concrete value; only defined if {@link #isConcrete()}. */
		public Rational getConcreteValue() {
			assert isConcrete();
			return mRational;
		}

		/**
		 * The congruence class of this value, or null for lambda and concrete values. For a CC-only value this is the
		 * representative; the value is the representative's value plus {@link #getOffsetToRep()}.
		 */
		public CCTerm getRepresentative() {
			return mRep;
		}

		/** The offset of a CC-only value to its representative. */
		public Rational getOffsetToRep() {
			assert mKind == Kind.CC_ONLY;
			return mRational;
		}

		/**
		 * The numeric value {@code this + offset}. Lambda under a non-zero offset is not supported, since lambda is
		 * only known to be smaller than everything else.
		 */
		public Value addOffset(final Rational offset) {
			assert mSort.isNumericSort();
			if (offset.equals(Rational.ZERO)) {
				return this;
			}
			switch (mKind) {
			case CONCRETE:
				return new Value(mSort, mKind, mRational.add(offset), null, 0);
			case CC_ONLY:
				return new Value(mSort, mKind, mRational.add(offset), mRep, mOrder);
			default:
				throw new UnsupportedOperationException("Offset on " + this);
			}
		}

		@Override
		public int compareTo(final Value other) {
			assert mSort.isNumericSort() && mSort == other.mSort;
			if (mKind != other.mKind) {
				return mKind.compareTo(other.mKind);
			}
			switch (mKind) {
			case LAMBDA:
				return 0;
			case CONCRETE:
				return mRational.compareTo(other.mRational);
			case CC_ONLY:
				if (mOrder != other.mOrder) {
					return Integer.compare(mOrder, other.mOrder);
				}
				return mRational.compareTo(other.mRational);
			default:
				throw new AssertionError("Comparing non-numeric values");
			}
		}

		@Override
		public boolean equals(final Object o) {
			if (!(o instanceof Value)) {
				return false;
			}
			final Value other = (Value) o;
			return mSort == other.mSort && mKind == other.mKind && mRep == other.mRep
					&& (mRational == null ? other.mRational == null : mRational.equals(other.mRational));
		}

		@Override
		public int hashCode() {
			return mSort.hashCode() * 31 + mKind.hashCode() * 7 + (mRep == null ? 0 : mRep.hashCode())
					+ (mRational == null ? 0 : mRational.hashCode());
		}

		@Override
		public String toString() {
			switch (mKind) {
			case LAMBDA:
				return "lambda";
			case CONCRETE:
				return mRational.toString();
			case CC_ONLY:
				return mRational.equals(Rational.ZERO) ? mRep.toString() : mRep + "+" + mRational;
			default:
				return mRep.toString();
			}
		}
	}

	/**
	 * A node of the trie that stores the corners of a function, one level per argument. The children are keyed by the
	 * argument value; numeric levels are sorted. A leaf (after the last argument) holds the corner.
	 */
	private static final class Node {
		final Map<Value, Node> mChildren;
		CCAppTerm mCorner;

		Node(final Sort argSort) {
			if (argSort == null) {
				mChildren = null;
			} else if (argSort.isNumericSort()) {
				mChildren = new TreeMap<>();
			} else {
				mChildren = new LinkedHashMap<>();
			}
		}
	}

	private final CClosure mClosure;
	private final ArrayTheory mArrayTheory;
	private final SharedTermEvaluator mEvaluator;
	private final Function<Sort, CCTerm> mLambdaTerms;
	/** The creation index of every representative; this is the order of CC-only values. */
	private final Map<CCTerm, Integer> mClassOrder = new HashMap<>();
	private final Map<FunctionSymbol, Node> mFuncModels = new HashMap<>();
	/** The piecewise-constant models of the weak representatives, built from their selects. */
	private final Map<ArrayTheory.ArrayNode, Node> mWeakRepModels = new HashMap<>();

	/**
	 * Build the model for the current state of the congruence closure. All ground theories must have finished their
	 * final check, so that congruence classes with the same concrete value at the same argument position are merged.
	 *
	 * @param closure
	 *            the congruence closure.
	 * @param arrayTheory
	 *            the array theory, or null if there are no arrays.
	 * @param evaluator
	 *            the evaluator for the values of LA shared terms.
	 * @param lambdaTerms
	 *            maps a sort to the CCTerm of its lambda, or to null if lambda of that sort has no CCTerm.
	 */
	public PiecewiseModel(final CClosure closure, final ArrayTheory arrayTheory, final SharedTermEvaluator evaluator,
			final Function<Sort, CCTerm> lambdaTerms) {
		mClosure = closure;
		mArrayTheory = arrayTheory;
		mEvaluator = evaluator;
		mLambdaTerms = lambdaTerms;
		int index = 0;
		for (final CCTerm term : closure.mAllTerms) {
			if (term.isRepresentative()) {
				mClassOrder.put(term, index++);
			}
		}
	}

	/** The symbolic value of a ground parameter in the current congruence closure. */
	public Value getValue(final CCParameter param) {
		final Sort sort = param.getCCTerm().getFlatTerm().getSort();
		final CCTerm rep = param.getRepresentative();
		final Rational offset = param.getOffsetToRep();
		final CCTerm lambda = mLambdaTerms.apply(sort);
		if (lambda != null && lambda.getRepresentative() == rep && isSymbolicLambda(rep)) {
			assert offset.equals(lambda.getOffsetToRep());
			return Value.lambda(sort);
		}
		if (!sort.isNumericSort()) {
			return new Value(sort, Value.Kind.CLASS, null, rep, 0);
		}
		final CCTerm shared = rep.getSharedTerm();
		if (shared != null) {
			// the shared term's value minus its offset to the representative is the representative's value
			final Rational repValue = mEvaluator.evaluate(shared.getFlatTerm(), sort.getTheory())
					.sub(shared.getOffsetToRep());
			return Value.concrete(sort, repValue.add(offset));
		}
		return new Value(sort, Value.Kind.CC_ONLY, offset, rep, mClassOrder.get(rep));
	}

	/**
	 * Check if the class of lambda can be treated as the symbolic lambda value, i.e., it is a singleton class without
	 * LA shared term. If an instance made lambda equal to another term or gave it an LA value, lambda is just an
	 * ordinary constant.
	 */
	static boolean isSymbolicLambda(final CCTerm lambdaRep) {
		return lambdaRep.getNumMembers() == 1 && lambdaRep.getSharedTerm() == null;
	}

	/**
	 * Find the corner whose value {@code f} has at the given arguments.
	 *
	 * @return the corner, or null if no corner covers the arguments, i.e., the value is lambda.
	 */
	public CCAppTerm getCorner(final FunctionSymbol func, final Value[] args) {
		assert args.length == func.getParameterSorts().length && args.length > 0;
		Node root = mFuncModels.get(func);
		if (root == null) {
			root = buildFunctionModel(func);
		}
		return findCorner(root, 0, args);
	}

	/**
	 * The corners of {@code f} in the order in which {@link #getCorner} searches them: numeric coordinates descending
	 * (lambda last), at other positions the classes before lambda. The value of {@code f} at some arguments is the
	 * value of the first corner in this list whose coordinates cover the arguments, i.e., every numeric coordinate is
	 * lambda or at most the argument, and every other coordinate is lambda or the class of the argument.
	 *
	 * @return the corners, empty if {@code f} has no ground application.
	 */
	public List<CCAppTerm> getCorners(final FunctionSymbol func) {
		Node root = mFuncModels.get(func);
		if (root == null) {
			root = buildFunctionModel(func);
		}
		final List<CCAppTerm> corners = new ArrayList<>();
		collectCorners(root, corners);
		return corners;
	}

	private void collectCorners(final Node node, final List<CCAppTerm> corners) {
		if (node.mChildren == null) {
			corners.add(node.mCorner);
			return;
		}
		if (node.mChildren instanceof TreeMap) {
			for (final Node child : ((TreeMap<Value, Node>) node.mChildren).descendingMap().values()) {
				collectCorners(child, corners);
			}
			return;
		}
		Node lambda = null;
		for (final Map.Entry<Value, Node> entry : node.mChildren.entrySet()) {
			if (entry.getKey().isLambda()) {
				lambda = entry.getValue();
			} else {
				collectCorners(entry.getValue(), corners);
			}
		}
		if (lambda != null) {
			collectCorners(lambda, corners);
		}
	}

	/** The symbolic value of {@code f} at the given arguments. */
	public Value evaluate(final FunctionSymbol func, final Value[] args) {
		final CCAppTerm corner = getCorner(func, args);
		return corner == null ? Value.lambda(func.getReturnSort()) : getValue(corner);
	}

	/**
	 * The symbolic value of {@code (select array index)}.
	 *
	 * <p>
	 * The weak representative of the array's weak equivalence class has a piecewise-constant model whose corners are
	 * the selects in its weak class, i.e., the selects whose weak-i representative is the weak representative. Below
	 * the smallest corner (or without a matching corner) the value is the default of the class: the value of a const
	 * array, the value the array theory fixed for finite sorts, or lambda. Every other array in the class is the weak
	 * representative with the stores on the path to it applied on top: at a store index whose weak-i representative is
	 * not the weak representative, the value is the select on that weak-i class, or lambda if there is none.
	 * </p>
	 *
	 * @param array
	 *            a ground array.
	 * @param index
	 *            the symbolic index.
	 * @return the value, or null if the array theory has no current weak equivalence graph.
	 */
	public Value evaluateSelect(final CCTerm array, final Value index) {
		if (mArrayTheory == null || mArrayTheory.mCongRoots == null) {
			return null;
		}
		final Sort elemSort = array.getFlatTerm().getSort().getArguments()[1];
		final ArrayTheory.ArrayNode node = mArrayTheory.mCongRoots.get(array.getRepresentative());
		final ArrayTheory.ArrayNode weakRep = node.getWeakRepresentative();
		for (ArrayTheory.ArrayNode n = node; n.mPrimaryEdge != null; n = n.mPrimaryEdge) {
			final CCParameter storeIndex = ArrayTheory.getIndexFromStore(n.mPrimaryStore);
			if (getValue(storeIndex).equals(index)) {
				final ArrayTheory.ArrayNode weakIRep = node.getWeakIRepresentative(storeIndex);
				if (weakIRep == weakRep) {
					// the stores on this index are undone on the way to the weak representative
					break;
				}
				final CCAppTerm select = weakIRep.mSelects.get(storeIndex.getValueKey());
				return select == null ? Value.lambda(elemSort) : getValue(select);
			}
		}
		Node model = mWeakRepModels.get(weakRep);
		if (model == null) {
			model = buildWeakRepModel(weakRep);
		}
		final CCAppTerm corner = findCorner(model, 0, new Value[] { index });
		return corner == null ? getArrayDefault(weakRep, elemSort) : getValue(corner);
	}

	private Node buildWeakRepModel(final ArrayTheory.ArrayNode weakRep) {
		final Sort indexSort = weakRep.mTerm.getFlatTerm().getSort().getArguments()[0];
		final Node root = new Node(indexSort);
		for (final CCAppTerm select : weakRep.mSelects.values()) {
			final Node leaf = root.mChildren.computeIfAbsent(getValue(ArrayTheory.getIndexFromSelect(select)),
					v -> new Node(null));
			if (leaf.mCorner == null) {
				leaf.mCorner = select;
			} else {
				// selects on the same index value in one weak-i class are equal after the final check
				assert leaf.mCorner.sameValueAs(select);
			}
		}
		mWeakRepModels.put(weakRep, root);
		return root;
	}

	private Value getArrayDefault(final ArrayTheory.ArrayNode weakRep, final Sort elemSort) {
		final CCParameter defaultValue = getArrayDefaultParam(weakRep);
		return defaultValue == null ? Value.lambda(elemSort) : getValue(defaultValue);
	}

	/**
	 * The default value of a weak equivalence class: the value of a const array, the value the array theory fixed for
	 * finite sorts, or null for lambda.
	 */
	private CCParameter getArrayDefaultParam(final ArrayTheory.ArrayNode weakRep) {
		if (weakRep.mConstTerm != null) {
			return ArrayTheory.getValueFromConst(weakRep.mConstTerm);
		}
		// for finite sorts the array theory chose a default value from the selects (computeWeakeqExt)
		final Map<CCParameter, Object> arrayModel =
				mArrayTheory.mArrayModels == null ? null : mArrayTheory.mArrayModels.get(weakRep);
		if (arrayModel != null && arrayModel.get(null) instanceof CCParameter) {
			return (CCParameter) arrayModel.get(null);
		}
		return null;
	}

	/**
	 * The piecewise-constant model of an array, as {@link #evaluateSelect} evaluates it: the corners and the default of
	 * its weak representative, and the stores applied on top.
	 */
	public static final class ArrayModel {
		/** The selects on the weak representative; a select whose index is lambda replaces the default. */
		public final List<CCAppTerm> mCorners = new ArrayList<>();
		/** The default value, or null for lambda. */
		public CCParameter mDefault;
		/** The indices of the stores applied on top, with distinct values. */
		public final List<CCParameter> mStoreIndices = new ArrayList<>();
		/** The values of the stores: the select on the weak-i class of the index, or null for lambda. */
		public final List<CCAppTerm> mStoreValues = new ArrayList<>();
	}

	/**
	 * The piecewise-constant model of a ground array.
	 *
	 * @param array
	 *            a ground array.
	 * @return the model of the array.
	 */
	public ArrayModel getArrayModel(final CCTerm array) {
		final ArrayModel result = new ArrayModel();
		final ArrayTheory.ArrayNode node = mArrayTheory.mCongRoots.get(array.getRepresentative());
		final ArrayTheory.ArrayNode weakRep = node.getWeakRepresentative();
		result.mCorners.addAll(weakRep.mSelects.values());
		result.mDefault = getArrayDefaultParam(weakRep);
		// the first store on an index value decides it, see evaluateSelect
		final List<Value> seen = new ArrayList<>();
		for (ArrayTheory.ArrayNode n = node; n.mPrimaryEdge != null; n = n.mPrimaryEdge) {
			final CCParameter storeIndex = ArrayTheory.getIndexFromStore(n.mPrimaryStore);
			final Value indexValue = getValue(storeIndex);
			if (seen.contains(indexValue)) {
				continue;
			}
			seen.add(indexValue);
			final ArrayTheory.ArrayNode weakIRep = node.getWeakIRepresentative(storeIndex);
			if (weakIRep != weakRep) {
				result.mStoreIndices.add(storeIndex);
				result.mStoreValues.add(weakIRep.mSelects.get(storeIndex.getValueKey()));
			}
		}
		return result;
	}

	private Node buildFunctionModel(final FunctionSymbol func) {
		final Sort[] argSorts = func.getParameterSorts();
		final Node root = new Node(argSorts[0]);
		for (final CCAppTerm app : mClosure.getAllFuncApps(func)) {
			Node node = root;
			for (int i = 0; i < argSorts.length; i++) {
				final Sort nextSort = i + 1 < argSorts.length ? argSorts[i + 1] : null;
				node = node.mChildren.computeIfAbsent(getValue(app.getArgParam(i)), v -> new Node(nextSort));
			}
			if (node.mCorner == null) {
				node.mCorner = app;
			} else {
				// applications with the same argument values are congruent after the final check
				assert node.mCorner.sameValueAs(app);
			}
		}
		mFuncModels.put(func, root);
		assert !Config.EXPENSIVE_ASSERTS || isCorrectForGroundApps(func);
		return root;
	}

	private CCAppTerm findCorner(final Node node, final int argPos, final Value[] args) {
		if (argPos == args.length) {
			return node.mCorner;
		}
		final Value arg = args[argPos];
		if (node.mChildren instanceof TreeMap) {
			// the greatest coordinate below the argument for which the remaining arguments are covered
			for (final Node child : ((TreeMap<Value, Node>) node.mChildren).headMap(arg, true).descendingMap()
					.values()) {
				final CCAppTerm corner = findCorner(child, argPos + 1, args);
				if (corner != null) {
					return corner;
				}
			}
			return null;
		}
		final Node exact = node.mChildren.get(arg);
		if (exact != null) {
			final CCAppTerm corner = findCorner(exact, argPos + 1, args);
			if (corner != null) {
				return corner;
			}
		}
		if (arg.isLambda()) {
			return null;
		}
		final Node lambda = node.mChildren.get(Value.lambda(arg.getSort()));
		return lambda == null ? null : findCorner(lambda, argPos + 1, args);
	}

	private boolean isCorrectForGroundApps(final FunctionSymbol func) {
		for (final CCAppTerm app : mClosure.getAllFuncApps(func)) {
			final Value[] args = new Value[app.getArgCount()];
			for (int i = 0; i < args.length; i++) {
				args[i] = getValue(app.getArgParam(i));
			}
			final CCAppTerm corner = getCorner(func, args);
			if (corner == null || !corner.sameValueAs(app)) {
				return false;
			}
		}
		return true;
	}
}
