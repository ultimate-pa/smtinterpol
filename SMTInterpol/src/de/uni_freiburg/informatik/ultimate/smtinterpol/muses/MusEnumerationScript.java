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
import java.util.HashMap;
import java.util.Map;
import java.util.Random;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.DoubleOption;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.EnumOption;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap.CopyMode;
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

	TimeoutHandler mHandler;

	ScopedArrayList<Term> mRememberedAssertions;
	int mCustomNameId;
	int mCurrentLevel;

	EnumOption<HeuristicsType> mInterpolationHeuristic;
	DoubleOption mTolerance;
	Random mRandom;

	public MusEnumerationScript(final SMTInterpol wrappedScript, final TerminationRequest request) {
		super(wrappedScript);
		mCustomNameId = 0;
		mCurrentLevel = 0;
		mHandler = new TimeoutHandler(request);
		mRandom = new Random((long) getOption(SMTLIBConstants.RANDOM_SEED));

		mInterpolationHeuristic = new EnumOption<>(HeuristicsType.RANDOM, true, HeuristicsType.class,
				"The Heuristic that is used to choose a minimal unsatisfiable subset/core for interpolant generation");
		mTolerance = new DoubleOption(0.9, true,
				"The tolerance value that is used by the SMALLESTAMONGWIDE and the WIDESTAMONGSMALL Heuristic.");
	}

	public MusEnumerationScript(final SMTInterpol wrappedScript) {
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

	/**
	 * Currently sets the timeout for the enumeration and for the selection and creation of the interpolant
	 * respectively, resulting in double the time of the given timeout, in worst case!
	 */
	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree) {
		final Translator translator = new Translator();
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), mHandler);
		final Map<String, Object> remusOptions = createSMTInterpolOptionsForReMus();
		final Script scriptForReMus = new SMTInterpol((SMTInterpol) mScript, remusOptions, CopyMode.CURRENT_VALUE);

		scriptForReMus.push(1);

		registerTermsForEnumeration(mRememberedAssertions, translator, engine, scriptForReMus);

		final UnexploredMap unexploredMap = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(scriptForReMus, translator);
		final int nrOfConstraints = solver.getNumberOfConstraints();
		final BitSet workingSet = new BitSet(nrOfConstraints);
		workingSet.flip(0, nrOfConstraints);
		final long timeout = (long) getOption(SMTInterpolOptions.TIMEOUT);

		final ReMus remus = new ReMus(solver, unexploredMap, workingSet, mHandler, timeout);
		final ArrayList<MusContainer> muses = remus.enumerate();
		remus.resetSolver();

		scriptForReMus.pop(1);

		mHandler.setTimeout(timeout/2);
		final MusContainer chosenMus = chooseMusAccordingToHeuristic(muses, mHandler);
		if (mHandler.isTerminationRequested()) {
			setOption(SMTInterpolOptions.TIMEOUT, timeout/2);
		}else {
			setOption(SMTInterpolOptions.TIMEOUT, mHandler.timeLeft() + timeout/2);
		}
		final Term[] sequenceOfInterpolants = getInterpolants(partition, startOfSubtree, chosenMus.getProof());
		setOption(SMTInterpolOptions.TIMEOUT, timeout);
		return sequenceOfInterpolants;
	}

	private Map<String, Object> createSMTInterpolOptionsForReMus() {
		final Map<String, Object> remusOptions = new HashMap<>();
		remusOptions.put(SMTLIBConstants.PRODUCE_MODELS, true);
		remusOptions.put(SMTLIBConstants.PRODUCE_PROOFS, true);
		remusOptions.put(SMTLIBConstants.INTERACTIVE_MODE, true);
		remusOptions.put(SMTLIBConstants.PRODUCE_UNSAT_CORES, true);
		return remusOptions;
	}

	private boolean hasName(final Term term) {
		if (term instanceof AnnotatedTerm) {
			final AnnotatedTerm annoTerm = (AnnotatedTerm) term;
			final Annotation[] annotations = annoTerm.getAnnotations();
			final String name = findName(annotations);
			if (name == null) {
				return false;
			}
			return true;
		} else {
			return false;
		}
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

	private AnnotatedTerm nameTerm(final Term term, final Script script) {
		final Annotation name = new Annotation(":named", "constraint" + Integer.toString(mCustomNameId));
		mCustomNameId++;
		return (AnnotatedTerm) script.annotate(term, name);
	}

	/**
	 * Declares the given terms to the 3 components in a proper manner, so that the components "know" those terms. For
	 * the scriptForReMus, this means, it has to "know" all terms in the sense of "All terms are annotated with a name
	 * and scriptForReMus knows about their annotation". Currently, this means that either scriptForReMus or the script
	 * it was cloned of, mScript, annotated the term with a name. For the translator this means, that each of the terms
	 * (necessarily named AnnotatedTerms!) is wrapped in a {@link NamedAtom} and this atom is declared with
	 * {@link Translator#declareConstraint(NamedAtom)}. For the DPLLEngine, this means that the preferred status of the
	 * atom is set and locked, and the atom is added with
	 * {@link DPLLEngine#addAtom(de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom)}.
	 */
	private void registerTermsForEnumeration(final ArrayList<Term> terms, final Translator translator,
			final DPLLEngine engine, final Script scriptForReMus) {
		AnnotatedTerm annoTerm;
		for (final Term term : terms) {
			if (hasName(term)) {
				annoTerm = (AnnotatedTerm) term;
			} else {
				annoTerm = nameTerm(term, scriptForReMus);
			}
			final NamedAtom atom = new NamedAtom(annoTerm, mCurrentLevel);
			atom.setPreferredStatus(atom.getAtom());
			atom.lockPreferredStatus();
			engine.addAtom(atom);
			translator.declareConstraint(atom);
		}
	}

	private MusContainer chooseMusAccordingToHeuristic(final ArrayList<MusContainer> muses, final TerminationRequest request) {
		MusContainer chosenMus;
		double tolerance;
		if (mRandom == null) {
			final long rndSeed = (long) getOption(SMTLIBConstants.RANDOM_SEED);
			mRandom = new Random(rndSeed);
		}
		switch (mInterpolationHeuristic.getValue()) {
		case RANDOM:
			chosenMus = Heuristics.chooseRandomMus(muses, mRandom);
			break;
		case SMALLEST:
			chosenMus = Heuristics.chooseSmallestMus(muses, mRandom, mHandler);
			break;
		case BIGGEST:
			chosenMus = Heuristics.chooseBiggestMus(muses, mRandom, mHandler);
			break;
		case LOWLEXORDER:
			chosenMus = Heuristics.chooseMusWithLowestLexicographicalOrder(muses, mRandom, mHandler);
			break;
		case HIGHLEXORDER:
			chosenMus = Heuristics.chooseMusWithHighestLexicographicalOrder(muses, mRandom, mHandler);
			break;
		case SHALLOWEST:
			chosenMus = Heuristics.chooseShallowestMus(muses, mRandom, mHandler);
			break;
		case DEEPEST:
			chosenMus = Heuristics.chooseDeepestMus(muses, mRandom, mHandler);
			break;
		case NARROWEST:
			chosenMus = Heuristics.chooseNarrowestMus(muses, mRandom, mHandler);
			break;
		case WIDEST:
			chosenMus = Heuristics.chooseWidestMus(muses, mRandom, mHandler);
			break;
		case SMALLESTAMONGWIDE:
			tolerance = (double) mTolerance.get();
			chosenMus = Heuristics.chooseSmallestAmongWideMuses(muses, tolerance, mRandom, mHandler);
			break;
		case WIDESTAMONGSMALL:
			tolerance = (double) mTolerance.get();
			chosenMus = Heuristics.chooseWidestAmongSmallMuses(muses, tolerance, mRandom, mHandler);
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
			mRememberedAssertions.beginScope();
		}
		mCurrentLevel = mCurrentLevel + levels;
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		super.pop(levels);
		for (int i = 0; i < levels; i++) {
			mRememberedAssertions.endScope();
		}
		mCurrentLevel = mCurrentLevel - levels;
	}

	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		if (opt.equals(":interpolation-heuristic")) {
			mInterpolationHeuristic.set(value);
		} else if (opt.equals(":tolerance")) {
			mTolerance.set(value);
		} else if (opt.equals(SMTLIBConstants.RANDOM_SEED)) {
			mScript.setOption(opt, value);
			mRandom = new Random((long) getOption(SMTLIBConstants.RANDOM_SEED));
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
	public void reset() {
		mScript.reset();
		mRememberedAssertions.clear();
		mCustomNameId = 0;
		mCurrentLevel = 0;
		mInterpolationHeuristic.reset();
		mTolerance.reset();
		mRandom = new Random((long) getOption(SMTLIBConstants.RANDOM_SEED));
	}

	@Override
	public void resetAssertions() {
		mScript.resetAssertions();
		mRememberedAssertions.clear();
	}
}
