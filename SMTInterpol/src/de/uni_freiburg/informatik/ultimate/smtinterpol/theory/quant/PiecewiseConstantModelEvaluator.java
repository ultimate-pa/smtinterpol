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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.ArrayTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;

/**
 * This class allows for evaluating terms in the current partial model where functions (and arrays) are piecewise
 * constant. A term f(x1,...,xn) is evaluated for a substitution (s1,...,sn) by projecting it on existing terms
 * f(t1,...,tn). The projection is found as follows: TODO
 * 
 * Terms should only be evaluated after all ground theory solvers have finished their final check.
 * 
 * @author Tanja Schindler
 *
 */
public class PiecewiseConstantModelEvaluator {

	private final QuantifierTheory mQuantTheory;

	private final Theory mTheory;
	private final Clausifier mClausifier;
	private final ArrayTheory mArrayTheory;
	private final CClosure mCClosure;

	private final List<TermVariable> mVars;
	private final List<Term> mSubstitution;

	private final Map<Term, CCTerm> mModelCClassReps;
	private final Map<SMTAffineTerm, Rational> mModelValues;

	private boolean mKnowsAllTerms;

	public PiecewiseConstantModelEvaluator(final QuantifierTheory quantTheory, final List<TermVariable> vars,
			final List<Term> subs) {
		mQuantTheory = quantTheory;

		mTheory = mQuantTheory.getTheory();
		mClausifier = mQuantTheory.getClausifier();
		mArrayTheory = mClausifier.getArrayTheory();
		mCClosure = mClausifier.getCClosure();

		mVars = vars;
		mSubstitution = subs;

		mModelCClassReps = new HashMap<>();
		mModelValues = new HashMap<>();
		mKnowsAllTerms = true;
	}

	/**
	 * For a given (possibly quantified) term, get the CC class that this term is evaluated to in the current model
	 * under the given substitution.
	 * 
	 * @param quantTerm
	 *            the (possibly quantified) term to evaluate in the CC model.
	 * @return the model CC class (potentially null for numeric terms).
	 */
	public CCTerm getModelCClass(final Term quantTerm) {
		// assert !quantTerm.getSort().isNumericSort();
		if (!mModelCClassReps.containsKey(quantTerm)) {
			findModelCClass(quantTerm);
		}
		assert mModelCClassReps.containsKey(quantTerm);
		return mModelCClassReps.get(quantTerm);
	}

	/**
	 * For a given (possibly quantified) affine term, get the Rational value that this term is evaluated to in the
	 * current model under the given substitution.
	 * 
	 * @param quantTerm
	 *            the (possibly quantified) affine term to evaluate in the LinAr model.
	 * @return the model Rational value (potentially -infinity, standing for a fresh value smaller than all the value of
	 *         all known terms).
	 */
	public Rational getModelValue(final SMTAffineTerm quantTerm) {
		if (!mModelValues.containsKey(quantTerm)) {
			findModelValue(quantTerm);
		}
		assert mModelValues.containsKey(quantTerm);
		return mModelValues.get(quantTerm);
	}

	public boolean knowsAllTerms() {
		return mKnowsAllTerms;
	}

	/**
	 * For a given (possibly quantified) term, get the Rational value that this term is evaluated to in the current
	 * model under the given substitution.
	 * 
	 * @param quantTerm
	 *            the (possibly quantified) term to evaluate in the LinAr model.
	 * @return the model Rational value (potentially -infinity, standing for a fresh value smaller than all the value of
	 *         all known terms).
	 */
	public Rational getModelValue(final Term term) {
		assert term.getSort().isNumericSort();
		final SMTAffineTerm affine = new SMTAffineTerm(term);
		return getModelValue(affine);
	}

	private void findModelValue(final SMTAffineTerm quantTerm) {
		Rational modelValue = Rational.ZERO;
		final SharedTermEvaluator evaluator = new SharedTermEvaluator(mClausifier);
		Rational lambdaCoeff = Rational.ZERO;
		for (final Entry<Term, Rational> smd : quantTerm.getSummands().entrySet()) {
			final Term term = smd.getKey();
			final Term lambda = mQuantTheory.getLambda(term.getSort());
			final Rational termValue;
			final Rational coeff = smd.getValue();
			if (term.getFreeVars().length == 0) {
				termValue = term == lambda ? Rational.NEGATIVE_INFINITY : evaluator.evaluate(term, mTheory);
			} else if (term instanceof TermVariable) {
				final Term subs = mSubstitution.get(mVars.indexOf(term));
				if (QuantUtil.isLambda(subs)) {
					termValue = Rational.NEGATIVE_INFINITY;
				} else {
					termValue = evaluator.evaluate(subs, mTheory);
				}
			} else {
				assert term instanceof ApplicationTerm;
				final CCTerm modelCClass = getModelCClass(term);
				final CCTerm lambdaCClass = mClausifier.getCCTerm(lambda).getRepresentative();
				if (modelCClass == lambdaCClass && !QuantUtil.isLambda(term)) {
					mKnowsAllTerms = false;
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
		modelValue = modelValue.add(quantTerm.getConstant());
		if (lambdaCoeff.signum() < 0) {
			modelValue = Rational.POSITIVE_INFINITY;
		} else if (lambdaCoeff.signum() > 0) {
			modelValue = Rational.NEGATIVE_INFINITY;
		}
		// TODO How do we want to deal with lambda-lambda+c (in the end, we will not build such instances anyway)
		assert !modelValue.equals(Rational.NAN);
		mModelValues.put(quantTerm, modelValue);
	}

	private void findModelCClass(final Term term) {
		if (!mModelCClassReps.containsKey(term)) {
			CCTerm modelCClass = null;
			final CCTerm lambdaCClass = mClausifier.getCCTerm(mQuantTheory.getLambda(term.getSort()));
			if (term.getFreeVars().length == 0) {
				modelCClass = mClausifier.getCCTerm(term);
			} else if (term instanceof TermVariable) {
				modelCClass = mClausifier.getCCTerm(mSubstitution.get(mVars.indexOf(term)));
			} else if (Clausifier.needCCTerm(term)) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				final FunctionSymbol func = appTerm.getFunction();
				Term[] args = appTerm.getParameters().clone();
				boolean isSelect = false;
				CCTerm weakIRep = null;
				CCTerm selectIndexModelCClass = null;
				Sort selectIndexSort = null;
				if (func.getName() == "select") { // We need to evaluate on the weak-i-representative
					isSelect = true;
					final CCTerm arrayModelCClass = getModelCClass(appTerm.getParameters()[0]);
					selectIndexModelCClass = getModelCClass(appTerm.getParameters()[1]);
					selectIndexSort = appTerm.getParameters()[1].getSort();
					assert selectIndexModelCClass != null || selectIndexSort.isNumericSort();
					final CCTerm indexLambdaCClass = mClausifier
							.getCCTerm(mQuantTheory.getLambda(selectIndexSort));
					weakIRep = mArrayTheory.getWeakIRep(arrayModelCClass,
							selectIndexModelCClass != null ? selectIndexModelCClass : indexLambdaCClass);
					assert weakIRep != null;
					args[0] = weakIRep.getFlatTerm();
				}
				// Collect a list of candidate model classes
				final List<CCTerm> candidates = new ArrayList<>();
				candidates.add(mCClosure.getFuncTerm(func).getRepresentative());
				for (int i = 0; i < args.length; i++) {
					final List<CCTerm> appCandidates = CClosure.getApplications(candidates);
					candidates.clear();
					if (appCandidates.isEmpty()) {
						break;
					} else {
						final Term arg = args[i];
						final Sort argSort = arg.getSort();
						if (isSelect && i == 0) {
							assert argSort.isArraySort();
							for (final CCTerm cand : appCandidates) {
								assert cand instanceof CCAppTerm;
								final CCTerm candArgRep = ((CCAppTerm) cand).getArg().getRepresentative();
								final CCTerm selectLambda = mClausifier
										.getCCTerm(mQuantTheory.getLambda(selectIndexSort));
								if (weakIRep == mArrayTheory.getWeakIRep(candArgRep,
										selectIndexModelCClass != null ? selectIndexModelCClass : selectLambda)) {
									candidates.add(cand);
								}
							}
						} else {
							final CCTerm argModelCClass = getModelCClass(arg);
							final Rational argModelValue = argSort.isNumericSort() ? getModelValue(arg) : null;
							assert argModelCClass != null || argSort.isNumericSort() && argModelValue != null;
							final Term argLambda = mQuantTheory.getLambda(argSort);
							final CCTerm argLambdaCClass = mClausifier.getCCTerm(argLambda).getRepresentative();
							for (final CCTerm cand : appCandidates) {
								assert cand instanceof CCAppTerm;
								final CCTerm candArgCClass = ((CCAppTerm) cand).getArg().getRepresentative();
								final Rational candArgValue = argSort.isNumericSort()
										? getModelValue(((CCAppTerm) cand).getArg().getFlatTerm())
										: null;
								if (argModelCClass == candArgCClass || candArgCClass == argLambdaCClass
										|| argSort.isNumericSort() && candArgValue.compareTo(argModelValue) <= 0) {
									candidates.add(cand);
								}
							}
						}
					}
				}

				// Find best match among candidates
				if (candidates.isEmpty()) {
					modelCClass = lambdaCClass;
				} else if (candidates.size() == 1) {
					modelCClass = candidates.get(0);
				} else {
					// For each argument, keep only the terms with the "closest" argument projection
					if (isSelect) {
						final Rational selectIndexValue =
								selectIndexSort.isNumericSort() ? getModelValue(appTerm.getParameters()[1]) : null;
						CCTerm bestArgProj =
								mClausifier.getCCTerm(mQuantTheory.getLambda(selectIndexSort)).getRepresentative();
						Rational bestArgProjValue = selectIndexSort.isNumericSort() ? Rational.NEGATIVE_INFINITY : null;
						// We only need to care about the index
						boolean changed = true;
						while (changed) {
							changed = false;
							final Iterator<CCTerm> it = candidates.iterator();
							while (it.hasNext()) {
								final CCTerm cand = it.next();
								assert cand instanceof CCAppTerm;
								final CCTerm candArgRep = ((CCAppTerm) cand).getArg().getRepresentative();
								final Rational candArgValue =
										selectIndexSort.isNumericSort() ? getModelValue(candArgRep.getFlatTerm())
												: null;
								if (candArgRep == selectIndexModelCClass && bestArgProj != selectIndexModelCClass) {
									bestArgProj = candArgRep; // exact match
									bestArgProjValue = candArgValue;
									changed = true;
								} else if (selectIndexSort.isNumericSort()
										&& candArgValue.compareTo(selectIndexValue) <= 0
										&& bestArgProjValue.compareTo(candArgValue) < 0) {
									bestArgProjValue = candArgValue; // greater lower bound than before
									changed = true;
								}
								if (!selectIndexSort.isNumericSort() && candArgRep != bestArgProj
										|| selectIndexSort.isNumericSort()
												&& candArgValue.compareTo(bestArgProjValue) < 0) {
									it.remove();
									changed = true;
								}
							}
								}
					} else {
						for (int i = 0; i < args.length; i++) {
							final Term arg = args[i];
							final Sort argSort = arg.getSort();
							final CCTerm argModelCClass = getModelCClass(arg);
							final Rational argModelValue = argSort.isNumericSort() ? getModelValue(arg) : null;
							assert argModelCClass != null || argSort.isNumericSort() && argModelValue != null;
							final Term argLambda = mQuantTheory.getLambda(argSort);
							final CCTerm argLambdaCClass = mClausifier.getCCTerm(argLambda).getRepresentative();
							CCTerm bestArgProj = argLambdaCClass;
							Rational bestArgProjValue = Rational.NEGATIVE_INFINITY;
							boolean changed = true;
							while (changed) {
								changed = false;
								final Iterator<CCTerm> it = candidates.iterator();
								while (it.hasNext()) {
									final CCTerm cand = it.next();
									assert cand instanceof CCAppTerm;
									CCAppTerm partialApp = (CCAppTerm) cand;
									for (int j = 0; j < func.getParameterSorts().length - i - 1; j++) {
										partialApp = (CCAppTerm) ((CCAppTerm) partialApp).getFunc();
									}
									final CCTerm candArgCClass = partialApp.getArg().getRepresentative();
									final Rational candArgValue = argSort.isNumericSort() ? getModelValue(partialApp.getArg().getFlatTerm()) : null;
									if (candArgCClass == argModelCClass && bestArgProj != argModelCClass) {
										// perfect match
										bestArgProj = candArgCClass;
										bestArgProjValue = candArgValue;
										changed = true;
									} else if (argSort.isNumericSort() && candArgValue.compareTo(argModelValue) <= 0
											&& bestArgProjValue.compareTo(candArgValue) < 0) {
										// greater lower bound
										bestArgProj = candArgCClass;
										bestArgProjValue = candArgValue;
										changed = true;
									}
									if (!argSort.isNumericSort() && candArgCClass != bestArgProj
											|| argSort.isNumericSort()
											&& candArgValue.compareTo(bestArgProjValue) < 0) {
										it.remove();
										changed = true;
									}
								}
							}
						}
						if (candidates.size() > 1) {
							assert areAllEquivalent(candidates);
						}
					}
					assert candidates.size() >= 1;
					modelCClass = candidates.get(0);
				}
				assert !modelCClass.isFunc();
				if (modelCClass == lambdaCClass && !QuantUtil.isLambda(term)) {
					mKnowsAllTerms = false;
				} else if (modelCClass instanceof CCAppTerm) {
					CCAppTerm partialApp = (CCAppTerm) modelCClass;
					for (int i = args.length - 1; i >= 0; i--) {
						final CCTerm argModelCClass = getModelCClass(args[i]);
						final CCTerm candModelCClass = partialApp.getArg().getRepresentative();
						mKnowsAllTerms &= candModelCClass == argModelCClass;
						partialApp = i == 0 ? null : (CCAppTerm) partialApp.getFunc();
					}
				}
			}
			assert term.getSort().isNumericSort() || modelCClass != null && !modelCClass.isFunc();
			mModelCClassReps.put(term, modelCClass == null ? null : modelCClass.getRepresentative());
		}
	}

	private boolean areAllEquivalent(final List<CCTerm> terms) {
		assert !terms.isEmpty();
		CCTerm rep = terms.get(0).getRepresentative();
		for (final CCTerm t : terms) {
			if (t.getRepresentative() != rep) {
				return false;
			}
		}
		return true;
	}

	@Override
	public String toString() {
		return "Vars: " + mVars + " Subs: " + mSubstitution + "\nCClasses: " + mModelCClassReps + "\nValues: "
				+ mModelValues;
	}
}
