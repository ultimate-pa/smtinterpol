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

import java.math.BigInteger;
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
	boolean mAssertedTermsAreUnsat;

	EnumOption<HeuristicsType> mInterpolationHeuristic;
	DoubleOption mTolerance;
	Random mRandom;

	public MusEnumerationScript(final SMTInterpol wrappedScript, final TerminationRequest request) {
		super(wrappedScript);
		mCustomNameId = 0;
		mAssertedTermsAreUnsat = false;
		mHandler = new TimeoutHandler(request);
		mRandom = new Random(getRandomSeed());
		mRememberedAssertions = new ScopedArrayList<>();

		mInterpolationHeuristic = new EnumOption<>(HeuristicsType.RANDOM, true, HeuristicsType.class,
				"The Heuristic that is used to choose a minimal unsatisfiable subset/core for interpolant generation");
		mTolerance = new DoubleOption(0.9, true,
				"The tolerance value that is used by the SMALLESTAMONGWIDE and the WIDESTAMONGSMALL Heuristic.");
	}

	private long getRandomSeed() {
		return ((BigInteger) getOption(SMTLIBConstants.RANDOM_SEED)).longValue();
	}

	private long getTimeout() {
		return ((BigInteger) getOption(SMTInterpolOptions.TIMEOUT)).longValue();
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
	 * This method first enumerates MUSes of the current asserted terms, then it applies a heuristic for choosing a MUS
	 * amongst them. Lastly, the proof of unsatisfiability of the chosen MUS is used to generate the Sequence of
	 * Interpolants that is returned. The timeout is currently split into 1/2 timeout for ReMus, 1/4 (+ what's left of
	 * ReMus' timeout) timeout for applying the heuristic, 1/4 (+ what's left of the heuristics' timeout) generating the
	 * interpolant. If the timeout for ReMus is exceeded, it returns the muses found so far. If the timeout for the
	 * heuristic is exceeded, it returns the best mus found so far wrt. the heuristic. If the timeout for generating the
	 * interpolant is exceeded, or the timeout for ReMus is exceeded, before any MUSes could be produced, an
	 * SMTLIBException is thrown.
	 *
	 * To set the used heuristic, use {@link #setOption(String, Object)} with the
	 * {@link MusOptions#INTERPOLATION_HEURISTIC} key and the respective {@link HeuristicsType} value. If you choose
	 * {@link HeuristicsType#SMALLESTAMONGWIDE} or {@link HeuristicsType#WIDESTAMONGSMALL}, you may also want to specify
	 * the value for the key {@link MusOptions#TOLERANCE} (for information about the tolerance, see
	 * {@link Heuristics#chooseWidestAmongSmallMuses(ArrayList, double, Random, TerminationRequest)} or
	 * {@link Heuristics#chooseSmallestAmongWideMuses(ArrayList, double, Random, TerminationRequest)}.
	 */
	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree) {
		if (!mAssertedTermsAreUnsat) {
			throw new SMTLIBException(
					"Asserted terms must be determined to be unsatisfiable before an interpolant can be generated. Call checkSat to determine satisfiability.");
		}

		final long timeout = getTimeout();

		final long timeoutForReMus = timeout / 2;
		mHandler.setTimeout(timeoutForReMus);
		final ArrayList<MusContainer> muses = executeReMus(mHandler);

		if (muses.isEmpty()) {
			throw new SMTLIBException("Timeout for ReMus exceeded before any muses could be found.");
		}

		final long timeoutForHeuristic;
		if (mHandler.timeLeft() <= 0) {
			timeoutForHeuristic = timeout / 4;
		} else {
			timeoutForHeuristic = timeout / 4 + mHandler.timeLeft();
		}

		mHandler.setTimeout(timeoutForHeuristic);
		final MusContainer chosenMus = chooseMusAccordingToHeuristic(muses, mHandler);

		if (mHandler.timeLeft() <= 0) {
			setOption(SMTInterpolOptions.TIMEOUT, timeout / 4);
		} else {
			setOption(SMTInterpolOptions.TIMEOUT, timeout / 4 + mHandler.timeLeft());
		}
		mHandler.clearTimeout();
		final Term[] sequenceOfInterpolants = getInterpolants(partition, startOfSubtree, chosenMus.getProof());
		setOption(SMTInterpolOptions.TIMEOUT, timeout);
		return sequenceOfInterpolants;
	}

	/**
	 * First, uses the ReMUS algorithm to enumerate MUSes of the set of asserted Terms (max. 3/4 of the timeout). Then,
	 * it searches for the best MUS according to the chosen heuristic (1/4 of the timeout + what's left of ReMus'
	 * timeout). If the first timeout is exceeded, the enumeration stops and the heuristic is applied to the MUSes found
	 * so far. If the second timeout is exceeded, the best MUS that has been found so far is returned. If ReMUS could
	 * not find any MUS in the given time, an arbitrary unsat core (i.e., the unsat core from the wrapped script) is
	 * returned, which is not necessarily minimal wrt. satisfiability.
	 *
	 * To set the used heuristic, use {@link #setOption(String, Object)} with the
	 * {@link MusOptions#INTERPOLATION_HEURISTIC} key and the respective {@link HeuristicsType} value. If you choose
	 * {@link HeuristicsType#SMALLESTAMONGWIDE} or {@link HeuristicsType#WIDESTAMONGSMALL}, you may also want to specify
	 * the value for the key {@link MusOptions#TOLERANCE} (for information about the tolerance, see
	 * {@link Heuristics#chooseWidestAmongSmallMuses(ArrayList, double, Random, TerminationRequest)} or
	 * {@link Heuristics#chooseSmallestAmongWideMuses(ArrayList, double, Random, TerminationRequest)}.
	 */
	@Override
	public Term[] getUnsatCore() {
		if (!mAssertedTermsAreUnsat) {
			throw new SMTLIBException(
					"Asserted Terms must be determined Unsat to return an unsat core. Call checkSat to determine satisfiability.");
		} else if (!((boolean) getOption(SMTLIBConstants.PRODUCE_UNSAT_CORES))) {
			throw new SMTLIBException("Unsat core production must be enabled.");
		}

		final Term[] alternativeUnsatCore = mScript.getUnsatCore();
		final Translator translator = new Translator();
		final long timeout = getTimeout();
		final long timeoutForReMus = 3 * timeout / 4;

		mHandler.setTimeout(timeoutForReMus);
		final ArrayList<MusContainer> muses = executeReMus(translator, mHandler);

		if (muses.isEmpty()) {
			return alternativeUnsatCore;
		}

		final long timeoutForHeuristic;
		if (mHandler.timeLeft() <= 0) {
			timeoutForHeuristic = timeout / 4;
		} else {
			timeoutForHeuristic = timeout / 4 + mHandler.timeLeft();
		}

		mHandler.setTimeout(timeoutForHeuristic);
		final MusContainer chosenMus = chooseMusAccordingToHeuristic(muses, mHandler);

		mHandler.clearTimeout();
		setOption(SMTInterpolOptions.TIMEOUT, timeout);

		return translator.translateToTerms(chosenMus.getMus());
	}

	/**
	 * Executes the ReMus algorithm on the currently asserted Terms, with the given TerminationRequest. If termination
	 * is requested, all MUSes that have been found so far are returned.
	 */
	private ArrayList<MusContainer> executeReMus(final TerminationRequest request) {
		final Translator translator = new Translator();
		return executeReMus(translator, request);
	}

	private ArrayList<MusContainer> executeReMus(final Translator translator, final TerminationRequest request) {
		if (translator.getNumberOfConstraints() != 0) {
			throw new SMTLIBException("Translator must be new.");
		}
		final TimeoutHandler handlerForReMus = new TimeoutHandler(mHandler);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), handlerForReMus);
		final Map<String, Object> remusOptions = createSMTInterpolOptionsForReMus();
		final Script scriptForReMus = new SMTInterpol((SMTInterpol) mScript, remusOptions, CopyMode.CURRENT_VALUE);
		// TODO: Somehow give the handlerForReMus to the scriptForRemus

		scriptForReMus.push(1);

		registerTermsForEnumeration(mRememberedAssertions, translator, engine, scriptForReMus);
		resetCustomNameId();

		final UnexploredMap unexploredMap = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(scriptForReMus, translator);
		final int nrOfConstraints = solver.getNumberOfConstraints();
		final BitSet workingSet = new BitSet(nrOfConstraints);
		workingSet.flip(0, nrOfConstraints);

		final ReMus remus = new ReMus(solver, unexploredMap, workingSet, handlerForReMus, 0);
		final ArrayList<MusContainer> muses = remus.enumerate();
		remus.resetSolver();

		scriptForReMus.pop(1);
		return muses;
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
			final NamedAtom atom = new NamedAtom(annoTerm, 0);
			atom.setPreferredStatus(atom.getAtom());
			atom.lockPreferredStatus();
			engine.addAtom(atom);
			translator.declareConstraint(atom);
		}
	}

	private MusContainer chooseMusAccordingToHeuristic(final ArrayList<MusContainer> muses,
			final TerminationRequest request) {
		MusContainer chosenMus;
		double tolerance;
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
	public LBool checkSat() {
		final LBool sat = mScript.checkSat();
		if (sat == LBool.UNSAT) {
			mAssertedTermsAreUnsat = true;
		}
		return sat;
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		super.push(levels);
		for (int i = 0; i < levels; i++) {
			mRememberedAssertions.beginScope();
		}
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		super.pop(levels);
		for (int i = 0; i < levels; i++) {
			mRememberedAssertions.endScope();
		}
		mAssertedTermsAreUnsat = false;
	}

	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		if (opt.equals(MusOptions.INTERPOLATION_HEURISTIC)) {
			mInterpolationHeuristic.set(value);
		} else if (opt.equals(MusOptions.TOLERANCE)) {
			mTolerance.set(value);
		} else if (opt.equals(SMTLIBConstants.RANDOM_SEED)) {
			mScript.setOption(opt, value);
			mRandom = new Random(getRandomSeed());
		} else {
			mScript.setOption(opt, value);
		}
	}

	@Override
	public Object getOption(final String opt) throws UnsupportedOperationException {
		if (opt.equals(MusOptions.INTERPOLATION_HEURISTIC)) {
			return mInterpolationHeuristic.get();
		} else if (opt.equals(MusOptions.TOLERANCE)) {
			return mTolerance.get();
		} else {
			return mScript.getOption(opt);
		}
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		mRememberedAssertions.add(term);
		mAssertedTermsAreUnsat = false;
		return mScript.assertTerm(term);
	}

	@Override
	public void reset() {
		mScript.reset();
		mRememberedAssertions.clear();
		mCustomNameId = 0;
		mAssertedTermsAreUnsat = false;
		mInterpolationHeuristic.reset();
		mTolerance.reset();
		mRandom = new Random(getRandomSeed());
	}

	@Override
	public void resetAssertions() {
		mScript.resetAssertions();
		mRememberedAssertions.clear();
		mAssertedTermsAreUnsat = false;
	}

	private void resetCustomNameId() {
		mCustomNameId = 0;
	}
}
