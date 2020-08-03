/*
 * Copyright (C) 2020 Leonard Fichtner
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Random;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.DoubleOption;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.EnumOption;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.LongOption;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolOptions;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TimeoutHandler;

/**
 * An implementation of a WrapperScript, which provides additional functionality in terms of MUS enumeration and
 * interpolation.
 *
 * @author LeonardFichtner
 *
 */
public class MusEnumerationScript extends WrapperScript {

	public enum HeuristicsType {
		RANDOM {
		},
		SMALLEST {
		},
		BIGGEST {
		},
		LOWLEXORDER {
		},
		HIGHLEXORDER {
		},
		SHALLOWEST {
		},
		DEEPEST {
		},
		NARROWEST {
		},
		WIDEST {
		},
		SMALLESTAMONGWIDE {
		},
		WIDESTAMONGSMALL {
		}
	}

	Translator mTranslator;
	TimeoutHandler mHandler;
	DPLLEngine mEngine;
	Script mScriptForReMus;
	int mCustomNameId;
	EnumOption<HeuristicsType> mInterpolationHeuristic;
	DoubleOption mTolerance;
	Random mRandom;

	public MusEnumerationScript(final Script wrappedScript, final TerminationRequest request) {
		super(wrappedScript);
		final TimeoutHandler mHandler = new TimeoutHandler(request);
		mTranslator = new Translator();
		mEngine = new DPLLEngine(new DefaultLogger(), mHandler);
		mScriptForReMus = new SMTInterpol(mHandler);
		mScriptForReMus.setOption(":produce-models", true);
		mScriptForReMus.setOption(":produce-proofs", true);
		mScriptForReMus.setOption(":interactive-mode", true);
		mScriptForReMus.setOption(":produce-unsat-cores", true);
		mCustomNameId = 0;
		mRandom = null;

		mInterpolationHeuristic = new EnumOption<>(HeuristicsType.RANDOM, true,
				HeuristicsType.class,
				"The Heuristic that is used to choose a minimal unsatisfiable subset/core for interpolant generation");
		mTolerance = new DoubleOption(0.9, true,
				"The tolerance value that is used by the SMALLESTAMONGWIDE and the WIDESTAMONGSMALL Heuristic.");
	}

	public MusEnumerationScript(final Script wrappedScript) {
		this(wrappedScript, null);
	}

	@Override
	public FunctionSymbol getFunctionSymbol(final String constructor) {
		return mScript.getFunctionSymbol(constructor);
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree, final Term proofTree) {
		return mScript.getInterpolants(partition, startOfSubtree, proofTree);
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree) {
		final UnexploredMap map = new UnexploredMap(mEngine, mTranslator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(mScriptForReMus, mTranslator);
		final int nrOfConstraints = solver.getNumberOfConstraints();
		final BitSet workingSet = new BitSet(nrOfConstraints);
		workingSet.flip(0, nrOfConstraints);
		final long timeout = ((LongOption) getOption(SMTInterpolOptions.TIMEOUT)).getValue();
		if (mRandom == null) {
			final long rndSeed = ((LongOption) getOption(SMTLIBConstants.RANDOM_SEED)).getValue();
			mRandom = new Random(rndSeed);
		}
		final ReMus remus = new ReMus(solver, map, workingSet, mHandler, timeout);
		final ArrayList<MusContainer> muses = remus.enumerate();
		MusContainer chosenMus;
		double tolerance;
		switch(mInterpolationHeuristic.getValue()) {
		case RANDOM:
			chosenMus = Heuristics.chooseRandomMus(muses, mRandom);
			break;
		case SMALLEST:
			chosenMus = Heuristics.chooseSmallestMus(muses, mRandom);
			break;
		case BIGGEST:
			chosenMus = Heuristics.chooseBiggestMus(muses, mRandom);
			break;
		case LOWLEXORDER:
			chosenMus = Heuristics.chooseMusWithLowestLexicographicalOrder(muses, mRandom);
			break;
		case HIGHLEXORDER:
			chosenMus = Heuristics.chooseMusWithHighestLexicographicalOrder(muses, mRandom);
			break;
		case SHALLOWEST:
			chosenMus = Heuristics.chooseShallowestMus(muses, mRandom);
			break;
		case DEEPEST:
			chosenMus = Heuristics.chooseDeepestMus(muses, mRandom);
			break;
		case NARROWEST:
			chosenMus = Heuristics.chooseNarrowestMus(muses, mRandom);
			break;
		case WIDEST:
			chosenMus = Heuristics.chooseWidestMus(muses, mRandom);
			break;
		case SMALLESTAMONGWIDE:
			tolerance = (double) mTolerance.get();
			chosenMus = Heuristics.chooseSmallestAmongWideMuses(muses, tolerance, mRandom);
			break;
		case WIDESTAMONGSMALL:
			tolerance = (double) mTolerance.get();
			chosenMus = Heuristics.chooseWidestAmongSmallMuses(muses, tolerance, mRandom);
			break;
		default:
			throw new SMTLIBException("Unknown Enum for Interpolation heuristic");
		}
		return getInterpolants(partition, startOfSubtree, chosenMus.getProof());
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		super.push(levels);
		mScriptForReMus.push(levels);
		for (int i = 0; i < levels; i++) {
			mEngine.push();
		}
		mTranslator.push(levels);
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		super.pop(levels);
		mScriptForReMus.pop(levels);
		mEngine.pop(levels);
		mTranslator.pop(levels);
	}

	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		if(opt.equals(":interpolation-heuristic")) {
			mInterpolationHeuristic.set(value);
		}else if(opt.equals(":tolerance")) {
			mTolerance.set(value);
		}else {
			mScript.setOption(opt, value);
		}
	}

	@Override
	public Object getOption(final String opt) throws UnsupportedOperationException {
		if(opt.equals(":interpolation-heuristic")) {
			return mInterpolationHeuristic.get();
		}else if(opt.equals(":tolerance")) {
			return mTolerance.get();
		}else {
			return mScript.getOption(opt);
		}
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		if (term instanceof AnnotatedTerm) {
			return mScript.assertTerm(term);
		}
		final Annotation name = new Annotation(":named", "constraint" + Integer.toString(mCustomNameId));
		mCustomNameId++;
		final Term annoTerm = annotate(term, name);
		return mScript.assertTerm(annoTerm);
	}

	@Override
	public Term annotate(final Term t, final Annotation... annotations) throws SMTLIBException {
		final AnnotatedTerm annotatedConstraint = (AnnotatedTerm) mScript.annotate(t, annotations);
		mScriptForReMus.annotate(t, annotations);
		final NamedAtom atom = new NamedAtom(annotatedConstraint, 0);
		atom.setPreferredStatus(atom.getAtom());
		atom.lockPreferredStatus();
		mEngine.addAtom(atom);
		mTranslator.declareConstraint(atom);
		return annotatedConstraint;
	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		mScript.setLogic(logic);
		mScriptForReMus.setLogic(logic);
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		mScript.setLogic(logic);
		mScriptForReMus.setLogic(logic);
	}

	@Override
	public void declareSort(final String sort, final int arity) throws SMTLIBException {
		mScript.declareSort(sort, arity);
		mScriptForReMus.declareSort(sort, arity);
	}

	@Override
	public void defineSort(final String sort, final Sort[] sortParams, final Sort definition) throws SMTLIBException {
		mScript.defineSort(sort, sortParams, definition);
		mScriptForReMus.defineSort(sort, sortParams, definition);
	}

	@Override
	public void declareDatatype(final DataType datatype, final DataType.Constructor[] constrs) throws SMTLIBException {
		mScript.declareDatatype(datatype, constrs);
		mScriptForReMus.declareDatatype(datatype, constrs);
	}

	@Override
	public void declareDatatypes(final DataType[] datatypes, final DataType.Constructor[][] constrs,
			final Sort[][] sortParams) throws SMTLIBException {
		mScript.declareDatatypes(datatypes, constrs, sortParams);
		mScriptForReMus.declareDatatypes(datatypes, constrs, sortParams);
	}

	@Override
	public void declareFun(final String fun, final Sort[] paramSorts, final Sort resultSort) throws SMTLIBException {
		mScript.declareFun(fun, paramSorts, resultSort);
		mScriptForReMus.declareFun(fun, paramSorts, resultSort);
	}

	@Override
	public void defineFun(final String fun, final TermVariable[] params, final Sort resultSort, final Term definition)
			throws SMTLIBException {
		mScript.defineFun(fun, params, resultSort, definition);
		mScriptForReMus.defineFun(fun, params, resultSort, definition);
	}

	@Override
	public void exit() {
		mScript.exit();
		mScriptForReMus.exit();
	}

	@Override
	public void reset() {
		mScript.reset();
		mScriptForReMus.reset();
	}

	@Override
	public void resetAssertions() {
		mScript.resetAssertions();
		mScriptForReMus.resetAssertions();
	}
}
