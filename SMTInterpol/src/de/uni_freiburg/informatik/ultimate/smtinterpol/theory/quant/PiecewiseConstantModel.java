/*
 * Copyright (C) 2021 University of Freiburg
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

import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NavigableMap;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.ArrayTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.InstantiationManager.InstanceValue;

/**
 * A piecewise constant model for a function {@code f(x1,...,xn)} assigns constant values to areas of the function's
 * domain. These areas are defined by their "corners", i.e., by the tuples {@code (c1,...,cn)} for which application
 * terms {@code f(c1,...,cn)} exist in the E-graph.
 *
 * <p>
 * If all {@code ai} are numeric, a tuple {@code (a1,...,an)} is assigned a value {@code f(c1,...,cn)} if
 * {@code (c1,...,cn)} is the greatest tuple according to the lexicographic order such that {@code f(c1,...,cn)} is in
 * the E-graph and {@code ai>=ci} for all i. The term {@code lambda} is smaller than any other term. If no such tuple
 * exists, the tuple is assigned the value {@code lambda}.
 *
 * For uninterpreted sorts, instead of {@code ai>=ci} we require that {@code ai} and {@code ci} are in the same
 * congruence class or {@code ci} is {@code lambda}.
 * </p>
 *
 * <p>
 * All ground theories must have finished their final check before building the piecewise constant model.
 * </p>
 *
 * @author Tanja Schindler
 *
 */
public class PiecewiseConstantModel {

	private final QuantifierTheory mQuantTheory;
	private final Theory mTheory;
	private final Clausifier mClausifier;
	private final Map<FunctionSymbol, PartialFunction> mFuncModels;
	private final Map<CCTerm, PartialFunction> mArrayModels;

	/**
	 * Build a new piecewise constant model. The ground theories must have finished their final check before.
	 *
	 * @param quantTheory
	 *            the quantifier theory solver
	 */
	public PiecewiseConstantModel(final QuantifierTheory quantTheory) {
		mQuantTheory = quantTheory;
		mTheory = mQuantTheory.getTheory();
		mClausifier = mQuantTheory.getClausifier();
		mFuncModels = new HashMap<>();
		mArrayModels = new HashMap<>();
	}

	public InstanceValue evaluateArithmeticalLiteral(final QuantLiteral qLit, final List<Term> subs) {
		assert qLit.isArithmetical();
		final SharedTermEvaluator evaluator = new SharedTermEvaluator(mClausifier);
		final Theory theory = mQuantTheory.getTheory();
		if (qLit instanceof QuantEquality) {
			final QuantEquality qEq = (QuantEquality) qLit;
			assert qEq.getLhs() instanceof TermVariable && qEq.getRhs().getFreeVars().length == 0;
			final Term leftSubs = subs.get(qLit.getClause().getVarIndex((TermVariable) qEq.getLhs()));
			if (QuantUtil.isLambda(leftSubs)) {
				return InstanceValue.FALSE;
			} else {
				if (evaluator.evaluate(leftSubs, theory).equals(evaluator.evaluate(qEq.getRhs(), theory))) {
					return InstanceValue.TRUE;
				} else {
					return InstanceValue.FALSE;
				}
			}
		} else {
			final Term[] termLtTerm = QuantUtil.getArithmeticalTermLtTerm(qLit, mClausifier.getTermCompiler());
			final Term groundLhs = termLtTerm[0].getFreeVars().length == 0 ? termLtTerm[0]
					: subs.get(qLit.getClause().getVarIndex((TermVariable) termLtTerm[0]));
			final Term groundRhs = termLtTerm[1].getFreeVars().length == 0 ? termLtTerm[1]
					: subs.get(qLit.getClause().getVarIndex((TermVariable) termLtTerm[1]));
			if (QuantUtil.isLambda(groundRhs)) {
				return InstanceValue.FALSE;
			} else {
				if (QuantUtil.isLambda(groundLhs)
						|| evaluator.evaluate(groundLhs, theory).compareTo(evaluator.evaluate(groundRhs, theory)) < 0) {
					return InstanceValue.TRUE;
				} else {
					return InstanceValue.FALSE;
				}
			}
		}
	}

	/**
	 * Evaluate a literal for a given substitution in the final check. The result can only be true or false; in the
	 * final check, everything can be evaluated.
	 *
	 * TODO: Should we first check if it is an E-matching literal as we have the equivalent terms then?
	 *
	 * @param quantLit
	 * @param substitution
	 * @return
	 */
	public InstanceValue evaluateLiteral(final QuantLiteral quantLit, final List<Term> subs) {
		InstanceValue litValue;
		final boolean isNeg = quantLit.isNegated();
		final QuantLiteral atom = quantLit.getAtom();
		if (atom instanceof QuantEquality) {
			final QuantEquality eq = (QuantEquality) atom;
			if (!eq.getLhs().getSort().isNumericSort()) {
				litValue = evaluateCCEquality(eq, subs);
			} else {
				litValue = evaluateLAEquality(eq, subs);
			}
		} else {
			litValue = evaluateBoundConstraint((QuantBoundConstraint) atom, subs);
		}

		if (isNeg) {
			litValue = litValue.negate();
		}
		assert litValue == InstanceValue.FALSE || litValue == InstanceValue.TRUE;
		return litValue;
	}

	private InstanceValue evaluateCCEquality(final QuantEquality qEq, final List<Term> subs) {
		final CCTerm leftCC = evaluateInCC(qEq.getLhs(), Arrays.asList(qEq.getClause().getVars()), subs);
		final CCTerm rightCC = evaluateInCC(qEq.getRhs(), Arrays.asList(qEq.getClause().getVars()), subs);
		assert leftCC != null && rightCC != null;
		if (mQuantTheory.getCClosure().isEqSet(leftCC, rightCC)) {
			return InstanceValue.TRUE;
		} else {
			return InstanceValue.FALSE; // In the final check, CC classes that are not equal are distinct.
		}
	}

	private InstanceValue evaluateLAEquality(final QuantEquality qEq, final List<Term> subs) {
		final SMTAffineTerm diff = new SMTAffineTerm(qEq.getLhs());
		diff.add(Rational.MONE, qEq.getRhs());
		final Rational value = evaluateInArith(diff, Arrays.asList(qEq.getClause().getVars()), subs);
		if (value == Rational.ZERO) {
			return InstanceValue.TRUE;
		} else {
			return InstanceValue.FALSE;
		}
	}

	private InstanceValue evaluateBoundConstraint(final QuantBoundConstraint qBc, final List<Term> subs) {
		final SMTAffineTerm affine = qBc.getAffineTerm();
		final Rational value = evaluateInArith(affine, Arrays.asList(qBc.getClause().getVars()), subs);
		if (value.compareTo(Rational.ZERO) <= 0) {
			return InstanceValue.TRUE;
		} else {
			return InstanceValue.FALSE;
		}
	}

	/**
	 * For a given (possibly quantified) term, get the CC class that this term evaluates to in the current model under
	 * the given substitution.
	 *
	 * @param term
	 *            the term to be evaluated (may contain variables)
	 * @param vars
	 *            a list of variables containing the variables of the term
	 * @param subs
	 *            a list of ground terms to be substituted for the variables (must have the same length)
	 * @return the model CC class (can be null for numeric terms)
	 */
	CCTerm evaluateInCC(final Term term, final List<Term> vars, final List<Term> subs) { // TODO: Non-recursive
		assert vars.size() == subs.size();
		final CCTerm ccModel;
		if (term.getFreeVars().length == 0) {
			ccModel = mClausifier.getCCTerm(term);
		} else if (term instanceof TermVariable) {
			assert vars.contains(term) && subs.get(vars.indexOf(term)).getFreeVars().length == 0;
			ccModel = mClausifier.getCCTerm(subs.get(vars.indexOf(term)));
		} else if (Clausifier.needCCTerm(term)) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol fsym = appTerm.getFunction();
			final Term[] args = appTerm.getParameters();
			if (fsym.getName() == "select") {
				final ArrayTheory arrayTheory = mClausifier.getArrayTheory();
				final Term arrayTerm = args[0];
				final CCTerm arrayCC = evaluateInCC(arrayTerm, vars, subs);
				final Term indexTerm = args[1];
				final Sort indexSort = indexTerm.getSort();
				final Object[] indexModel;
				final CCTerm indexCC;
				if (indexSort.isNumericSort()) {
					final Rational indexValue = evaluateInArith(indexTerm, vars, subs);
					final Set<CCTerm> storeIndicesTowardsWeakRep = arrayTheory.getStoreIndicesTowardsWeakRep(arrayCC);
					final SharedTermEvaluator evaluator = new SharedTermEvaluator(mClausifier);
					CCTerm matchingStoreIndex = null;
					for (final CCTerm idx : storeIndicesTowardsWeakRep) {
						if (indexValue == evaluator.evaluate(idx.getFlatTerm(), mQuantTheory.getTheory())) {
							matchingStoreIndex = idx;
							break;
						}
					}
					indexCC = matchingStoreIndex;
					indexModel = new Rational[] { indexValue };
				} else {
					indexCC = evaluateInCC(indexTerm, vars, subs);
					indexModel = new CCTerm[] { indexCC };
				}
				// if weakIRep has a select, take this select
				final CCTerm weakIRepSelect = indexCC == null ? null : arrayTheory.getWeakIRepSelect(arrayCC, indexCC);
				if (weakIRepSelect != null) {
					ccModel = weakIRepSelect;
				} else {
					final CCTerm weakRep = arrayTheory.getWeakRep(arrayCC);
					final CCTerm weakIRep = indexCC == null ? null : arrayTheory.getWeakIRep(arrayCC, indexCC);
					if (weakIRep == null || weakRep == weakIRep) { // evaluate in weakRep model (pw constant)
						if (!mArrayModels.containsKey(weakRep)) {
							buildArrayModelWeakRep(weakRep);
						}
						final PartialFunction arrayModel = mArrayModels.get(weakRep);
						final CCTerm model = findModel(arrayModel, 0, indexModel, new Sort[] { indexSort });
						ccModel = model != null ? model : mClausifier.getCCTerm(mQuantTheory.getLambdaOrDefaultTerm(term.getSort()));
					} else { // else take arbitrary value
						// TODO Use fresh value if value domain is infinite, to avoid extensionality
						ccModel = mClausifier.getCCTerm(mQuantTheory.getLambdaOrDefaultTerm(appTerm.getSort()));
					}
				}
			} else {
				if (!mFuncModels.containsKey(fsym)) {
					buildUninterpretedFunctionModel(fsym);
				}
				final PartialFunction funcModel = mFuncModels.get(fsym);
				assert funcModel != null;
				if (funcModel.isComplete()) { // default value
					assert funcModel.mNumArgs == fsym.getParameterSorts().length;
					ccModel = funcModel.mModelValue;
				} else {
					final Object[] argModels = new Object[args.length];
					final Sort[] argSorts = new Sort[args.length];
					for (int i = 0; i < args.length; i++) {
						final Term a = args[i];
						final Sort aSort = a.getSort();
						argSorts[i] = aSort;
						if (aSort.isNumericSort()) {
							argModels[i] = evaluateInArith(a, vars, subs);
						} else {
							argModels[i] = evaluateInCC(a, vars, subs);
						}
					}
					final CCTerm model = findModel(funcModel, 0, argModels, argSorts);
					ccModel = model != null ? model : mClausifier.getCCTerm(mQuantTheory.getLambdaOrDefaultTerm(term.getSort()));
				}
			}
		} else {
			assert term.getSort().isNumericSort();
			ccModel = null;
		}
		return ccModel == null ? null : ccModel.getRepresentative();
	}

	/**
	 * For a given (possibly quantified) term, get the Rational value that this term evaluates to in the current model
	 * under the given substitution.
	 *
	 * @param term
	 *            the term to be evaluated (may contain variables)
	 * @param vars
	 *            a list of variables containing the variables of the term
	 * @param subs
	 *            a list of ground terms to be substituted for the variables (must have the same length)
	 * @return the model Rational (where -infinity stands for a fresh value smaller than all values of known terms)
	 */
	private Rational evaluateInArith(final Term term, final List<Term> vars, final List<Term> subs) {
		assert term.getSort().isNumericSort();
		return evaluateInArith(new SMTAffineTerm(term), vars, subs);
	}

	/**
	 * For a given (possibly quantified) affine term, get the Rational value that this term evaluates to in the current
	 * model under the given substitution.
	 *
	 * @param affTerm
	 *            the affine term to be evaluated (may contain variables)
	 * @param vars
	 *            a list of variables containing the variables of the term
	 * @param subs
	 *            a list of ground terms to be substituted for the variables (must have the same length)
	 * @return the model Rational (where -infinity stands for a fresh value smaller than all values of known terms)
	 */
	private Rational evaluateInArith(final SMTAffineTerm affTerm, final List<Term> vars, final List<Term> subs) {
		assert vars.size() == subs.size();
		Rational modelValue = Rational.ZERO;
		final SharedTermEvaluator evaluator = new SharedTermEvaluator(mClausifier);
		Rational lambdaCoeff = Rational.ZERO;
		for (final Entry<Term, Rational> smd : affTerm.getSummands().entrySet()) {
			final Term term = smd.getKey();
			final Term lambda = mQuantTheory.getLambdaOrDefaultTerm(term.getSort());
			final Rational termValue;
			final Rational coeff = smd.getValue();
			if (term.getFreeVars().length == 0) {
				termValue = term == lambda ? Rational.NEGATIVE_INFINITY : evaluator.evaluate(term, mTheory);
			} else if (term instanceof TermVariable) {
				assert vars.contains(term) && subs.get(vars.indexOf(term)).getFreeVars().length == 0;
				final Term ts = subs.get(vars.indexOf(term));
				termValue = ts == lambda ? Rational.NEGATIVE_INFINITY : evaluator.evaluate(ts, mTheory);
			} else {
				assert term instanceof ApplicationTerm;
				final CCTerm modelCClass = evaluateInCC(term, vars, subs);
				final CCTerm lambdaCClass = mClausifier.getCCTerm(lambda).getRepresentative();
				if (modelCClass == lambdaCClass && term != lambda) {
					termValue = Rational.NEGATIVE_INFINITY;
				} else {
					termValue = evaluator.evaluate(modelCClass.getFlatTerm(), mTheory);
				}
			}
			if (termValue == Rational.NEGATIVE_INFINITY) {
				lambdaCoeff = lambdaCoeff.add(coeff);
			} else {
				modelValue = modelValue.addmul(coeff, termValue);
			}
		}
		modelValue = modelValue.add(affTerm.getConstant());
		if (lambdaCoeff.signum() < 0) {
			modelValue = Rational.POSITIVE_INFINITY;
		} else if (lambdaCoeff.signum() > 0) {
			modelValue = Rational.NEGATIVE_INFINITY;
		}
		// TODO Deal with lambda-lambda+c (we will not build such instances)
		assert !modelValue.equals(Rational.NAN);
		return modelValue;
	}

	private void buildUninterpretedFunctionModel(final FunctionSymbol fsym) {
		assert !mFuncModels.containsKey(fsym);
		long time;
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		final int nArgs = fsym.getParameterSorts().length;
		assert nArgs > 0;

		final List<CCTerm> allTotalApps = mQuantTheory.getCClosure().getAllFuncApps(fsym);
		if (allTotalApps.isEmpty()) { // Set to default value lambda
			mFuncModels.put(fsym,
					new PartialFunction(nArgs, mClausifier.getCCTerm(mQuantTheory.getLambdaOrDefaultTerm(fsym.getReturnSort()))));
		} else {
			final Sort firstArgSort = fsym.getParameterSorts()[0];
			final PartialFunction funcModel = new PartialFunction(nArgs, firstArgSort);
			for (final CCTerm app : allTotalApps) {
				final ApplicationTerm appTerm = (ApplicationTerm) app.getFlatTerm();
				PartialFunction partialFunc = funcModel;
				for (int i = 0; i < appTerm.getParameters().length; i++) {
					final Term arg = appTerm.getParameters()[i];
					final Sort argSort = arg.getSort();
					final PartialFunction nextPartialFunc = i == nArgs - 1 ? new PartialFunction(0, app)
							: new PartialFunction(nArgs - (i + 1), fsym.getParameterSorts()[i + 1]);
					if (argSort.isNumericSort()) {
						assert partialFunc.isNumeric();
						final Rational argModel = QuantUtil.isLambda(arg) ? Rational.NEGATIVE_INFINITY
								: new SharedTermEvaluator(mClausifier).evaluate(arg, mQuantTheory.getTheory());
						if (!partialFunc.mNumericArgFunctions.containsKey(argModel)) {
							partialFunc.mNumericArgFunctions.put(argModel, nextPartialFunc);
						}
						partialFunc = partialFunc.mNumericArgFunctions.get(argModel);
					} else {
						assert partialFunc.isUninterpreted();
						final CCTerm argRep = mClausifier.getCCTerm(arg).getRepresentative();
						assert argRep != null;
						if (!partialFunc.mUninterpretedArgFunctions.containsKey(argRep)) {
							partialFunc.mUninterpretedArgFunctions.put(argRep, nextPartialFunc);
						}
						partialFunc = partialFunc.mUninterpretedArgFunctions.get(argRep);
					}
					if (i == nArgs - 1) {
						assert partialFunc.isComplete()
						&& partialFunc.mModelValue.getRepresentative() == app.getRepresentative();
					}
				}
			}
			mFuncModels.put(fsym, funcModel);
		}
		assert !Config.EXPENSIVE_ASSERTS || isCorrectModelForGroundApps(fsym);
		if (Config.PROFILE_TIME) {
			mQuantTheory.addBuildModelTime(System.nanoTime() - time);
		}
	}

	private void buildArrayModelWeakRep(final CCTerm arrayWeakRep) {
		assert !mArrayModels.containsKey(arrayWeakRep);
		final Sort arraySort = arrayWeakRep.getFlatTerm().getSort();
		assert arraySort.isArraySort();
		assert arrayWeakRep == mClausifier.getArrayTheory().getWeakRep(arrayWeakRep);
		final Sort valueSort = arraySort.getArguments()[1];
		final Map<CCTerm, CCAppTerm> weakRepSelects = mClausifier.getArrayTheory().getWeakRepSelects(arrayWeakRep);
		if (weakRepSelects.isEmpty()) {
			mArrayModels.put(arrayWeakRep,
					new PartialFunction(1, mClausifier.getCCTerm(mQuantTheory.getLambdaOrDefaultTerm(valueSort))));
			// TODO Use unique value to avoid extensionality if value domain is infinite
		} else {
			final Sort indexSort = arraySort.getArguments()[0];
			final PartialFunction arrayModel = new PartialFunction(1, indexSort);
			for (final Entry<CCTerm, CCAppTerm> select : weakRepSelects.entrySet()) {
				final CCTerm selectIndex = select.getKey();
				final CCTerm selectVal = select.getValue();
				final PartialFunction constSelectCCFunction = new PartialFunction(0, selectVal);
				if (indexSort.isNumericSort()) {
					final Term indexTerm = selectIndex.getFlatTerm();
					final Rational indexVal = QuantUtil.isLambda(indexTerm) ? Rational.NEGATIVE_INFINITY
							: new SharedTermEvaluator(mClausifier).evaluate(indexTerm, mQuantTheory.getTheory());
					if (!arrayModel.mNumericArgFunctions.containsKey(indexVal)) {
						arrayModel.mNumericArgFunctions.put(indexVal, constSelectCCFunction);
					} else {
						assert arrayModel.mNumericArgFunctions.get(indexVal).mModelValue
						.getRepresentative() == selectVal.getRepresentative();
					}
				} else {
					final CCTerm indexRep = selectIndex.getRepresentative();
					if (!arrayModel.mUninterpretedArgFunctions.containsKey(indexRep)) {
						arrayModel.mUninterpretedArgFunctions.put(indexRep, constSelectCCFunction);
					} else {
						assert arrayModel.mUninterpretedArgFunctions.get(indexRep).mModelValue
						.getRepresentative() == selectVal.getRepresentative();
					}
				}
			}
			mArrayModels.put(arrayWeakRep, arrayModel);
		}
	}

	// TODO Non-recursive
	private CCTerm findModel(final PartialFunction funcModel, final int argNum, final Object[] argModels,
			final Sort[] argSorts) {
		assert funcModel.mNumArgs == argModels.length - argNum;
		if (argNum == argModels.length) {
			assert funcModel.isComplete();
			return funcModel.mModelValue;
		} else if (funcModel.isComplete()) {
			assert QuantUtil.isLambda(funcModel.mModelValue.getFlatTerm());
			return funcModel.mModelValue;
		}
		CCTerm model = null;
		if (argModels[argNum] instanceof Rational) {
			assert funcModel.isNumeric();
			final Rational aModel = (Rational) argModels[argNum];
			final NavigableMap<Rational, PartialFunction> headMapReversed =
					funcModel.mNumericArgFunctions.headMap(aModel, true).descendingMap();
			final Iterator<PartialFunction> it = headMapReversed.values().iterator();
			while (model == null && it.hasNext()) {
				model = findModel(it.next(), argNum + 1, argModels, argSorts);
			}
		} else {
			assert argModels[argNum] instanceof CCTerm;
			assert funcModel.isUninterpreted();
			final CCTerm argCCRep = ((CCTerm) argModels[argNum]).getRepresentative();
			final PartialFunction argFunction = funcModel.mUninterpretedArgFunctions.get(argCCRep);
			if (argFunction != null) {
				model = findModel(argFunction, argNum + 1, argModels, argSorts);
			}
			if (model == null) {
				final CCTerm lambdaRep =
						mClausifier.getCCTerm(mQuantTheory.getLambdaOrDefaultTerm(argSorts[argNum])).getRepresentative();
				final PartialFunction lambdaArgFunction = funcModel.mUninterpretedArgFunctions.get(lambdaRep);
				if (lambdaArgFunction != null) {
					model = findModel(lambdaArgFunction, argNum + 1, argModels, argSorts);
				}
			}
		}
		return model;
	}

	private boolean isCorrectModelForGroundApps(final FunctionSymbol fsym) {
		final List<CCTerm> allApps = mQuantTheory.getCClosure().getAllFuncApps(fsym);
		for (final CCTerm app : allApps) {
			PartialFunction funcModel = mFuncModels.get(fsym);
			if (funcModel == null) {
				return false;
			}
			final ApplicationTerm appTerm = (ApplicationTerm) app.getFlatTerm();
			for (final Term arg : appTerm.getParameters()) {
				PartialFunction argModel = null;
				if (arg.getSort().isNumericSort() && funcModel.mNumericArgFunctions != null) {
					final Rational argValue = QuantUtil.isLambda(arg) ? Rational.NEGATIVE_INFINITY
							: new SharedTermEvaluator(mClausifier).evaluate(arg, mTheory);
					argModel = funcModel.mNumericArgFunctions.get(argValue);
				} else if (funcModel.mUninterpretedArgFunctions != null) {
					final CCTerm argRep = mClausifier.getCCTerm(arg).getRepresentative();
					argModel = funcModel.mUninterpretedArgFunctions.get(argRep);
				}
				funcModel = argModel;
				if (argModel == null) {
					return false;
				}
			}
			// check the final value
			if (!funcModel.isComplete()) {
				return false;
			}
			final CCTerm modelCC = funcModel.mModelValue;
			if (app.getRepresentative() != modelCC.getRepresentative()) {
				return false;
			}
		}
		return true;
	}

	private class PartialFunction {
		final int mNumArgs;
		final CCTerm mModelValue;
		final TreeMap<Rational, PartialFunction> mNumericArgFunctions;
		final Map<CCTerm, PartialFunction> mUninterpretedArgFunctions;

		PartialFunction(final int nArgs, final CCTerm modelValue) {
			if (modelValue == null) {
				throw new IllegalArgumentException("The model value of a complete function must not be null.");
			}
			mNumArgs = nArgs;
			mModelValue = modelValue;
			mNumericArgFunctions = null;
			mUninterpretedArgFunctions = null;
		}

		PartialFunction(final int nArgs, final Sort sort) {
			if (sort == null) {
				throw new IllegalArgumentException("The argument sort for a partial function must not be null.");
			}
			mNumArgs = nArgs;
			mModelValue = null;
			if (sort.isNumericSort()) {
				mNumericArgFunctions = new TreeMap<Rational, PartialFunction>();
				mUninterpretedArgFunctions = null;
			} else {
				mNumericArgFunctions = null;
				mUninterpretedArgFunctions = new HashMap<CCTerm, PartialFunction>();
			}
		}

		boolean isComplete() {
			return mModelValue != null;
		}

		boolean isNumeric() {
			return mNumericArgFunctions != null;
		}

		boolean isUninterpreted() {
			return mUninterpretedArgFunctions != null;
		}
	}
}
