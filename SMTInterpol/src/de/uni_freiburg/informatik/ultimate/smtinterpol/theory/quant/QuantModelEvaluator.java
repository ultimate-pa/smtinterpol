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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCParameter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.PiecewiseModel;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.PiecewiseModel.Value;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LASharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;

/**
 * Evaluates quantified clauses under a substitution in the piecewise-constant model of the current final check (see
 * {@code doc/piecewise-constant-models.md}).
 *
 * <p>
 * Uninterpreted functions and {@code @AUX} predicates are evaluated in the {@link PiecewiseModel}, arithmetic
 * symbolically as a linear combination of concrete values, CC-only classes and lambda. Whenever the symbolic value
 * domain cannot decide a literal (e.g., a sum of several CC-only classes, non-linear arithmetic, or interpreted
 * functions that are not supported), the literal is {@link Result#UNKNOWN}; the caller must then treat the clause as
 * not satisfied by the model.
 * </p>
 *
 * @author Jochen Hoenicke
 */
class QuantModelEvaluator {

	enum Result {
		TRUE, FALSE, UNKNOWN
	}

	/** Thrown when the symbolic model cannot determine a value. */
	private static final class UnknownValue extends RuntimeException {
		private static final long serialVersionUID = 1L;
		static final UnknownValue INSTANCE = new UnknownValue();

		@Override
		public synchronized Throwable fillInStackTrace() {
			return this;
		}
	}

	/**
	 * A symbolic linear combination {@code constant + sum(coeff * class) + lambdaCoeff * lambda}, where the classes are
	 * the representatives of CC-only classes.
	 */
	private final class Sum {
		Rational mConstant = Rational.ZERO;
		Rational mLambdaCoeff = Rational.ZERO;
		final Map<CCTerm, Rational> mClasses = new LinkedHashMap<>();

		void add(final Rational factor, final Value value) {
			if (value.isLambda()) {
				mLambdaCoeff = mLambdaCoeff.addmul(factor, Rational.ONE);
			} else if (value.isConcrete()) {
				mConstant = mConstant.addmul(factor, value.getConcreteValue());
			} else {
				final CCTerm rep = value.getRepresentative();
				final Rational old = mClasses.get(rep);
				final Rational coeff = old == null ? factor : old.add(factor);
				if (coeff.equals(Rational.ZERO)) {
					mClasses.remove(rep);
				} else {
					mClasses.put(rep, coeff);
				}
				mConstant = mConstant.addmul(factor, value.getOffsetToRep());
			}
		}

		void add(final Rational factor, final Sum other) {
			mConstant = mConstant.addmul(factor, other.mConstant);
			mLambdaCoeff = mLambdaCoeff.addmul(factor, other.mLambdaCoeff);
			for (final Entry<CCTerm, Rational> entry : other.mClasses.entrySet()) {
				final Rational old = mClasses.get(entry.getKey());
				final Rational coeff = old == null ? factor.mul(entry.getValue()) : old.addmul(factor, entry.getValue());
				if (coeff.equals(Rational.ZERO)) {
					mClasses.remove(entry.getKey());
				} else {
					mClasses.put(entry.getKey(), coeff);
				}
			}
		}

		/**
		 * The sign of the sum. Lambda is below everything, a CC-only class above all concrete values, and of two CC-only
		 * classes the later one is above the earlier one plus any offset (the order of {@link PiecewiseModel.Value}).
		 */
		int signum() {
			if (mLambdaCoeff.signum() != 0) {
				return -mLambdaCoeff.signum();
			}
			switch (mClasses.size()) {
			case 0:
				return mConstant.signum();
			case 1:
				return mClasses.values().iterator().next().signum();
			case 2:
				final Iterator<Entry<CCTerm, Rational>> it = mClasses.entrySet().iterator();
				final Entry<CCTerm, Rational> first = it.next();
				final Entry<CCTerm, Rational> second = it.next();
				if (!first.getValue().equals(second.getValue().negate())) {
					throw UnknownValue.INSTANCE;
				}
				final int cmp = mModel.getValue(first.getKey()).compareTo(mModel.getValue(second.getKey()));
				return cmp > 0 ? first.getValue().signum() : second.getValue().signum();
			default:
				throw UnknownValue.INSTANCE;
			}
		}

		/** Convert to a value of the given sort, if the sum is a single value. */
		Value toValue(final Sort sort) {
			if (mLambdaCoeff.signum() != 0) {
				if (mLambdaCoeff.equals(Rational.ONE) && mClasses.isEmpty() && mConstant.equals(Rational.ZERO)) {
					return Value.lambda(sort);
				}
				throw UnknownValue.INSTANCE;
			}
			if (mClasses.isEmpty()) {
				return Value.concrete(sort, mConstant);
			}
			if (mClasses.size() == 1) {
				final Entry<CCTerm, Rational> entry = mClasses.entrySet().iterator().next();
				if (entry.getValue().equals(Rational.ONE) && entry.getKey().getFlatTerm().getSort() == sort) {
					return mModel.getValue(CCParameter.of(entry.getKey(), mConstant));
				}
			}
			throw UnknownValue.INSTANCE;
		}
	}

	private final QuantifierTheory mQuantTheory;
	private final Clausifier mClausifier;
	private final CClosure mClosure;
	private final Theory mTheory;
	private final PiecewiseModel mModel;
	private final CCTerm mTrueTerm;
	/** The values of ground terms; valid for this model. */
	private final Map<Term, Value> mGroundValues = new HashMap<>();

	private QuantClause mClause;
	private List<Term> mSubs;

	QuantModelEvaluator(final QuantifierTheory quantTheory) {
		mQuantTheory = quantTheory;
		mClausifier = quantTheory.getClausifier();
		mClosure = quantTheory.getCClosure();
		mTheory = quantTheory.getTheory();
		mModel = new PiecewiseModel(mClosure, mClausifier.getArrayTheory(), new SharedTermEvaluator(mClausifier),
				sort -> sort == mTheory.getBooleanSort() ? null : mClausifier.getCCTerm(quantTheory.getLambda(sort)));
		mTrueTerm = mClausifier.getCCTerm(mTheory.mTrue);
	}

	/**
	 * Evaluate a quantified clause under a substitution.
	 *
	 * @return TRUE if some literal is true in the model, FALSE if all literals are false, UNKNOWN otherwise.
	 */
	Result evaluateClause(final QuantClause clause, final List<Term> subs) {
		for (final Literal groundLit : clause.getGroundLits()) {
			if (groundLit.getAtom().getDecideStatus() == groundLit) {
				return Result.TRUE;
			}
		}
		mClause = clause;
		mSubs = subs;
		Result result = Result.FALSE;
		for (final QuantLiteral lit : clause.getQuantLits()) {
			final Result litResult = evaluateLiteral(lit);
			if (litResult == Result.TRUE) {
				return Result.TRUE;
			} else if (litResult == Result.UNKNOWN) {
				result = Result.UNKNOWN;
			}
		}
		return result;
	}

	private Result evaluateLiteral(final QuantLiteral lit) {
		boolean value;
		try {
			value = evaluateAtom(lit.getAtom());
		} catch (final UnknownValue e) {
			return Result.UNKNOWN;
		}
		return value != lit.isNegated() ? Result.TRUE : Result.FALSE;
	}

	private boolean evaluateAtom(final QuantLiteral atom) {
		if (atom instanceof QuantEquality) {
			final QuantEquality eq = (QuantEquality) atom;
			return evaluateEquality(eq.getLhs(), eq.getRhs());
		}
		final Polynomial poly = ((QuantBoundConstraint) atom).getAffineTerm();
		return evaluateSum(poly).signum() <= 0;
	}

	private boolean evaluateEquality(final Term lhs, final Term rhs) {
		final Sort sort = lhs.getSort();
		if (sort.isNumericSort()) {
			final Sum diff = evaluateSum(new Polynomial(lhs));
			diff.add(Rational.MONE, evaluateSum(new Polynomial(rhs)));
			return diff.signum() == 0;
		}
		if (sort == mTheory.getBooleanSort()) {
			return evaluateFormula(lhs) == evaluateFormula(rhs);
		}
		final Value lhsValue = evaluateValue(lhs);
		final Value rhsValue = evaluateValue(rhs);
		if (lhsValue.equals(rhsValue)) {
			return true;
		}
		if (sort.isArraySort()) {
			// different congruence classes can still be extensionally equal
			throw UnknownValue.INSTANCE;
		}
		return false;
	}

	private Sum evaluateSum(final Polynomial poly) {
		final Sum sum = new Sum();
		for (final Entry<Map<Term, Integer>, Rational> monom : poly.getSummands().entrySet()) {
			final Map<Term, Integer> factors = monom.getKey();
			if (factors.isEmpty()) {
				sum.mConstant = sum.mConstant.add(monom.getValue());
			} else if (factors.size() == 1 && factors.values().iterator().next() == 1) {
				Term factor = factors.keySet().iterator().next();
				if (Polynomial.isToReal(factor)) {
					factor = ((ApplicationTerm) factor).getParameters()[0];
				}
				sum.add(monom.getValue(), evaluateNumericAtom(factor));
			} else {
				throw UnknownValue.INSTANCE;
			}
		}
		return sum;
	}

	/** Evaluate a numeric term that is not a sum or product, i.e., a variable, constant, or application. */
	private Sum evaluateNumericAtom(final Term term) {
		final Sum sum = new Sum();
		if (term instanceof TermVariable || term.getFreeVars().length == 0) {
			sum.add(Rational.ONE, evaluateValue(term));
		} else {
			sum.add(Rational.ONE, evaluateApplication((ApplicationTerm) term));
		}
		return sum;
	}

	/** Evaluate a term (of any sort) to a single value. */
	private Value evaluateValue(final Term term) {
		final Sort sort = term.getSort();
		if (sort == mTheory.getBooleanSort()) {
			return booleanValue(evaluateFormula(term));
		}
		if (term instanceof TermVariable) {
			return evaluateGround(mSubs.get(mClause.getVarIndex((TermVariable) term)));
		}
		if (term.getFreeVars().length == 0) {
			return evaluateGround(term);
		}
		if (sort.isNumericSort() && !isUninterpretedApp(term)) {
			return evaluateSum(new Polynomial(term)).toValue(sort);
		}
		return evaluateApplication((ApplicationTerm) term);
	}

	private Value evaluateGround(final Term term) {
		Value value = mGroundValues.get(term);
		if (value == null) {
			value = computeGroundValue(term);
			mGroundValues.put(term, value);
		}
		return value;
	}

	private Value computeGroundValue(final Term term) {
		final Sort sort = term.getSort();
		final CCParameter param = mClosure.getCCParamRep(term);
		if (param != null) {
			// this also decides whether lambda is still symbolic
			return mModel.getValue(param);
		}
		if (QuantUtil.isLambda(term)) {
			return Value.lambda(sort);
		}
		if (sort.isNumericSort()) {
			final LASharedTerm laTerm = mClausifier.getLATerm(term);
			if (laTerm != null) {
				Rational value = laTerm.getOffset();
				for (final Entry<LinVar, Rational> entry : laTerm.getSummands().entrySet()) {
					value = value.addmul(entry.getValue(), mClausifier.getLASolver().realValue(entry.getKey()));
				}
				return Value.concrete(sort, value);
			}
			final Polynomial poly = new Polynomial(term);
			if (!isUninterpretedApp(term) && !isSingleAtom(poly, term)) {
				return evaluateSum(poly).toValue(sort);
			}
		}
		if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getParameters().length > 0) {
			return evaluateApplication((ApplicationTerm) term);
		}
		// a constant without CC or LA term is unconstrained
		throw UnknownValue.INSTANCE;
	}

	/** Check if the polynomial is just the term itself, i.e., the term is not a sum or product. */
	private static boolean isSingleAtom(final Polynomial poly, final Term term) {
		final Map<Map<Term, Integer>, Rational> summands = poly.getSummands();
		if (summands.size() != 1) {
			return false;
		}
		final Entry<Map<Term, Integer>, Rational> monom = summands.entrySet().iterator().next();
		return monom.getValue().equals(Rational.ONE) && monom.getKey().size() == 1
				&& monom.getKey().get(term) != null && monom.getKey().get(term) == 1;
	}

	private static boolean isUninterpretedApp(final Term term) {
		if (!(term instanceof ApplicationTerm)) {
			return false;
		}
		final FunctionSymbol func = ((ApplicationTerm) term).getFunction();
		return !func.isIntern() || func.getName().startsWith("@AUX") || func.getName() == SMTLIBConstants.SELECT
				|| func.getName() == SMTLIBConstants.ITE;
	}

	private Value evaluateApplication(final ApplicationTerm app) {
		final FunctionSymbol func = app.getFunction();
		final Term[] params = app.getParameters();
		if (func.getName() == SMTLIBConstants.SELECT) {
			return evaluateSelect(params[0], evaluateValue(params[1]));
		}
		if (func.getName() == SMTLIBConstants.ITE) {
			return evaluateFormula(params[0]) ? evaluateValue(params[1]) : evaluateValue(params[2]);
		}
		if (params.length > 0 && (!func.isIntern() || func.getName().startsWith("@AUX"))) {
			final Value[] args = new Value[params.length];
			for (int i = 0; i < params.length; i++) {
				args[i] = evaluateValue(params[i]);
			}
			return mModel.evaluate(func, args);
		}
		throw UnknownValue.INSTANCE;
	}

	private Value evaluateSelect(final Term array, final Value index) {
		if (array.getFreeVars().length > 0 && array instanceof ApplicationTerm
				&& ((ApplicationTerm) array).getFunction().getName() == SMTLIBConstants.STORE) {
			// a store with a quantified part has no congruence class
			final Term[] params = ((ApplicationTerm) array).getParameters();
			if (evaluateValue(params[1]).equals(index)) {
				return evaluateValue(params[2]);
			}
			return evaluateSelect(params[0], index);
		}
		final Value arrayValue = evaluateValue(array);
		if (arrayValue.getRepresentative() == null) {
			throw UnknownValue.INSTANCE;
		}
		final Value value = mModel.evaluateSelect(arrayValue.getRepresentative(), index);
		if (value == null) {
			throw UnknownValue.INSTANCE;
		}
		return value;
	}

	private Value booleanValue(final boolean value) {
		return mModel.getValue(mClausifier.getCCTerm(value ? mTheory.mTrue : mTheory.mFalse));
	}

	private boolean evaluateFormula(final Term term) {
		if (term == mTheory.mTrue) {
			return true;
		}
		if (term == mTheory.mFalse) {
			return false;
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm app = (ApplicationTerm) term;
			final Term[] params = app.getParameters();
			switch (app.getFunction().getName()) {
			case SMTLIBConstants.NOT:
				return !evaluateFormula(params[0]);
			case SMTLIBConstants.AND:
				for (final Term p : params) {
					if (!evaluateFormula(p)) {
						return false;
					}
				}
				return true;
			case SMTLIBConstants.OR:
				for (final Term p : params) {
					if (evaluateFormula(p)) {
						return true;
					}
				}
				return false;
			case SMTLIBConstants.IMPLIES:
				for (int i = 0; i < params.length - 1; i++) {
					if (!evaluateFormula(params[i])) {
						return true;
					}
				}
				return evaluateFormula(params[params.length - 1]);
			case SMTLIBConstants.XOR: {
				boolean result = false;
				for (final Term p : params) {
					result ^= evaluateFormula(p);
				}
				return result;
			}
			case SMTLIBConstants.ITE:
				return evaluateFormula(params[0]) ? evaluateFormula(params[1]) : evaluateFormula(params[2]);
			case SMTLIBConstants.EQUALS:
				for (int i = 0; i < params.length - 1; i++) {
					if (!evaluateEquality(params[i], params[i + 1])) {
						return false;
					}
				}
				return true;
			case SMTLIBConstants.DISTINCT:
				for (int i = 0; i < params.length; i++) {
					for (int j = i + 1; j < params.length; j++) {
						if (evaluateEquality(params[i], params[j])) {
							return false;
						}
					}
				}
				return true;
			case SMTLIBConstants.LEQ:
			case SMTLIBConstants.LT:
			case SMTLIBConstants.GEQ:
			case SMTLIBConstants.GT:
				return evaluateComparison(app.getFunction().getName(), params);
			default:
				break;
			}
		}
		// a Boolean variable, constant, or predicate application: compare its class with true
		final Value value;
		if (term instanceof TermVariable) {
			value = evaluateGround(mSubs.get(mClause.getVarIndex((TermVariable) term)));
		} else if (term.getFreeVars().length == 0) {
			final CCParameter param = mClosure.getCCParamRep(term);
			if (param == null) {
				if (isUninterpretedApp(term) && ((ApplicationTerm) term).getParameters().length > 0) {
					value = evaluateApplication((ApplicationTerm) term);
				} else {
					throw UnknownValue.INSTANCE;
				}
			} else {
				value = mModel.getValue(param);
			}
		} else {
			value = evaluateApplication((ApplicationTerm) term);
		}
		return value.getRepresentative() == mTrueTerm.getRepresentative();
	}

	private boolean evaluateComparison(final String op, final Term[] params) {
		for (int i = 0; i < params.length - 1; i++) {
			final Sum diff = evaluateSum(new Polynomial(params[i]));
			diff.add(Rational.MONE, evaluateSum(new Polynomial(params[i + 1])));
			final int sign = diff.signum();
			final boolean holds;
			switch (op) {
			case SMTLIBConstants.LEQ:
				holds = sign <= 0;
				break;
			case SMTLIBConstants.LT:
				holds = sign < 0;
				break;
			case SMTLIBConstants.GEQ:
				holds = sign >= 0;
				break;
			default:
				holds = sign > 0;
				break;
			}
			if (!holds) {
				return false;
			}
		}
		return true;
	}

	QuantifierTheory getQuantTheory() {
		return mQuantTheory;
	}
}
