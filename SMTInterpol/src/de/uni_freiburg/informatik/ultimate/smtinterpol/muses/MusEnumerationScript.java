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
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedArrayList;

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

	private class Operation {
		String mName;
		Object mParam1;
		Object mParam2;
		Object mParam3;
		Object mParam4;

		private Operation(final String name, final Object param1, final Object param2, final Object param3,
				final Object param4) {
			mName = name;
			mParam1 = param1;
			mParam2 = param2;
			mParam3 = param3;
			mParam4 = param4;
		}

		public String getName() {
			return mName;
		}

		public Object getParam1() {
			return mParam1;
		}

		public Object getParam2() {
			return mParam2;
		}

		public Object getParam3() {
			return mParam3;
		}

		public Object getParam4() {
			return mParam4;
		}
	}

	UnexploredMap mUnexploredMap;
	ConstraintAdministrationSolver mSolver;
	TimeoutHandler mHandler;

	TerminationRequest mTerminationRequest;
	ScopedArrayList<Operation> mRememberedOperations;
	ScopedArrayList<Term> mRememberedAssertions;
	int mCustomNameId;
	int mCurrentLevel;

	EnumOption<HeuristicsType> mInterpolationHeuristic;
	DoubleOption mTolerance;
	Random mRandom;

	public MusEnumerationScript(final Script wrappedScript, final TerminationRequest request) {
		super(wrappedScript);
		mCustomNameId = 0;
		mCurrentLevel = 0;
		mTerminationRequest = request;
		mRememberedOperations = new ScopedArrayList<>();
		mRandom = null;
		mHandler = null;
		mSolver = null;
		mUnexploredMap = null;

		mInterpolationHeuristic = new EnumOption<>(HeuristicsType.RANDOM, true, HeuristicsType.class,
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
		setUpComponentsForEnumeration();
		final int nrOfConstraints = mSolver.getNumberOfConstraints();
		final BitSet workingSet = new BitSet(nrOfConstraints);
		workingSet.flip(0, nrOfConstraints);
		final long timeout = ((LongOption) getOption(SMTInterpolOptions.TIMEOUT)).getValue();

		final ReMus remus = new ReMus(mSolver, mUnexploredMap, workingSet, mHandler, timeout);
		clearComponentsForEnumeration();
		final ArrayList<MusContainer> muses = remus.enumerate();
		final MusContainer chosenMus = chooseMusAccordingToHeuristic(muses);
		return getInterpolants(partition, startOfSubtree, chosenMus.getProof());
	}

	private void setUpComponentsForEnumeration() {
		mHandler = new TimeoutHandler(mTerminationRequest);
		final Translator translator = new Translator();
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), mHandler);
		final Script scriptForReMus = new SMTInterpol(mHandler);
		scriptForReMus.setLogic(mScript.getTheory().getLogic());
		scriptForReMus.setOption(":produce-models", true);
		scriptForReMus.setOption(":produce-proofs", true);
		scriptForReMus.setOption(":interactive-mode", true);
		scriptForReMus.setOption(":produce-unsat-cores", true);
		for (final Operation op : mRememberedOperations) {
			switch (op.getName()) {
			case "annotate":
				final Term term = (Term) op.getParam1();
				final Annotation anno = (Annotation) op.getParam2();
				scriptForReMus.annotate(term, anno);
				break;
			case "declareSort":
				final String sort = (String) op.getParam1();
				final int arity = (int) op.getParam2();
				scriptForReMus.declareSort(sort, arity);
				break;
			case "defineSort":
				final String defSortSort = (String) op.getParam1();
				final Sort[] sortParams = (Sort[]) op.getParam2();
				final Sort definition = (Sort) op.getParam3();
				scriptForReMus.defineSort(defSortSort, sortParams, definition);
				break;
			case "declareDatatype":
				final DataType datatype = (DataType) op.getParam1();
				final DataType.Constructor[] constrs = (DataType.Constructor[]) op.getParam2();
				scriptForReMus.declareDatatype(datatype, constrs);
				break;
			case "declareDatatypes":
				final DataType[] datatypes = (DataType[]) op.getParam1();
				final DataType.Constructor[][] declDataTypesConstrs = (DataType.Constructor[][]) op.getParam2();
				final Sort[][] declDataTypesSortParams = (Sort[][]) op.getParam3();
				scriptForReMus.declareDatatypes(datatypes, declDataTypesConstrs, declDataTypesSortParams);
				break;
			case "declareFun":
				final String fun = (String) op.getParam1();
				final Sort[] paramSorts = (Sort[]) op.getParam2();
				final Sort resultSort = (Sort) op.getParam3();
				scriptForReMus.declareFun(fun, paramSorts, resultSort);
				break;
			case "defineFun":
				final String defFunFun = (String) op.getParam1();
				final TermVariable[] params = (TermVariable[]) op.getParam2();
				final Sort defFunResultSort = (Sort) op.getParam3();
				final Term defFunDefinition = (Term) op.getParam4();
				scriptForReMus.defineFun(defFunFun, params, defFunResultSort, defFunDefinition);
				break;
			default:
				throw new SMTLIBException("An unknown Operation has been remembered. A case for it should be added.");
			}
		}
		for (final Term term : mRememberedAssertions) {
			if (term instanceof AnnotatedTerm) {
				final AnnotatedTerm annoTerm = (AnnotatedTerm) term;
				final Annotation[] annotations = annoTerm.getAnnotations();
				final String name = findName(annotations);
				if (name == null) {
					// What to do here? Annotate again with a name?
				}
				registerAnnotatedTermForEnumeration(annoTerm, engine, translator);
			} else {
				final Annotation name = new Annotation(":named", "constraint" + Integer.toString(mCustomNameId));
				mCustomNameId++;
				final AnnotatedTerm annoTerm = (AnnotatedTerm) scriptForReMus.annotate(term, name);
				registerAnnotatedTermForEnumeration(annoTerm, engine, translator);
			}
		}
		mUnexploredMap = new UnexploredMap(engine, translator);
		mSolver = new ConstraintAdministrationSolver(scriptForReMus, translator);
	}

	private String findName(final Annotation[] annotations) {
		String name = null;
		for (int i = 0; i < annotations.length; i++) {
			if (annotations[i].getKey().equals(":named")) {
				name = (String) annotations[i].getValue();
			}
		}
		return name;
	}

	private void registerAnnotatedTermForEnumeration(final AnnotatedTerm term, final DPLLEngine engine,
			final Translator translator) {
		// To be fully "registered" this annotated Term must have been created by the script for remus,
		// but this should have been done earlier.
		final NamedAtom atom = new NamedAtom(term, mCurrentLevel);
		atom.setPreferredStatus(atom.getAtom());
		atom.lockPreferredStatus();
		engine.addAtom(atom);
		translator.declareConstraint(atom);
	}

	private void clearComponentsForEnumeration() {
		mHandler = null;
		mSolver = null;
		mUnexploredMap = null;
	}

	private MusContainer chooseMusAccordingToHeuristic(final ArrayList<MusContainer> muses) {
		MusContainer chosenMus;
		double tolerance;
		if (mRandom == null) {
			final long rndSeed = ((LongOption) getOption(SMTLIBConstants.RANDOM_SEED)).getValue();
			mRandom = new Random(rndSeed);
		}
		switch (mInterpolationHeuristic.getValue()) {
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
		return chosenMus;
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		super.push(levels);
		for (int i = 0; i < levels; i++) {
			mRememberedOperations.beginScope();
		}
		mCurrentLevel = mCurrentLevel + levels;
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		super.pop(levels);
		for (int i = 0; i < levels; i++) {
			mRememberedOperations.endScope();
		}
		mCurrentLevel = mCurrentLevel - levels;
	}

	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		if (opt.equals(":interpolation-heuristic")) {
			mInterpolationHeuristic.set(value);
		} else if (opt.equals(":tolerance")) {
			mTolerance.set(value);
		} else {
			mScript.setOption(opt, value);
		}
	}

	@Override
	public Object getOption(final String opt) throws UnsupportedOperationException {
		if (opt.equals(":interpolation-heuristic")) {
			return mInterpolationHeuristic.get();
		} else if (opt.equals(":tolerance")) {
			return mTolerance.get();
		} else {
			return mScript.getOption(opt);
		}
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		mRememberedAssertions.add(term);
		return mScript.assertTerm(term);
	}

	@Override
	public Term annotate(final Term t, final Annotation... annotations) throws SMTLIBException {
		mRememberedOperations.add(new Operation("annotate", t, annotations, null, null));
		return mScript.annotate(t, annotations);
	}

	@Override
	public void declareSort(final String sort, final int arity) throws SMTLIBException {
		mRememberedOperations.add(new Operation("declareSort", sort, arity, null, null));
		mScript.declareSort(sort, arity);
	}

	@Override
	public void defineSort(final String sort, final Sort[] sortParams, final Sort definition) throws SMTLIBException {
		mRememberedOperations.add(new Operation("defineSort", sort, sortParams, definition, null));
		mScript.defineSort(sort, sortParams, definition);
	}

	@Override
	public void declareDatatype(final DataType datatype, final DataType.Constructor[] constrs) throws SMTLIBException {
		mRememberedOperations.add(new Operation("declareDatatype", datatype, constrs, null, null));
		mScript.declareDatatype(datatype, constrs);
	}

	@Override
	public void declareDatatypes(final DataType[] datatypes, final DataType.Constructor[][] constrs,
			final Sort[][] sortParams) throws SMTLIBException {
		mRememberedOperations.add(new Operation("declareDatatypes", datatypes, constrs, sortParams, null));
		mScript.declareDatatypes(datatypes, constrs, sortParams);
	}

	@Override
	public void declareFun(final String fun, final Sort[] paramSorts, final Sort resultSort) throws SMTLIBException {
		mRememberedOperations.add(new Operation("declareFun", fun, paramSorts, resultSort, null));
		mScript.declareFun(fun, paramSorts, resultSort);
	}

	@Override
	public void defineFun(final String fun, final TermVariable[] params, final Sort resultSort, final Term definition)
			throws SMTLIBException {
		mRememberedOperations.add(new Operation("defineFun", fun, params, resultSort, definition));
		mScript.defineFun(fun, params, resultSort, definition);
	}

	@Override
	public void reset() {
		mScript.reset();
		mRememberedOperations.clear();
		mCustomNameId = 0;
		mCurrentLevel = 0;
		mInterpolationHeuristic.reset();
		mTolerance.reset();

	}

	@Override
	public void resetAssertions() {
		mScript.resetAssertions();
		mRememberedAssertions.clear();
	}
}
