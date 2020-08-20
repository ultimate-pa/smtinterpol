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
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.BooleanOption;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.DoubleOption;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.EnumOption;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.LongOption;
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

	/**
	 * For the exact meaning of the respective Heuristic, see the respective descriptions in {@link Heuristics}. That
	 * class does not contain the "FIRST" heuristic. The "FIRST" Heuristic means to just enumerate one MUS and generate
	 * the Interpolant from it.
	 */
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
		},
		FIRST {
		}
	}

	TimeoutHandler mHandler;

	ScopedArrayList<Term> mRememberedAssertions;
	int mCustomNameId;
	boolean mAssertedTermsAreUnsat;

	EnumOption<HeuristicsType> mInterpolationHeuristic;
	DoubleOption mTolerance;
	LongOption mEnumerationTimeout;
	LongOption mHeuristicTimeout;
	BooleanOption mLogAdditionalInformation;
	LogProxy mLogger;

	Random mRandom;

	public MusEnumerationScript(final SMTInterpol wrappedScript) {
		super(wrappedScript);
		assert wrappedScript instanceof SMTInterpol : "Currently, only SMTInterpol is supported.";
		final SMTInterpol wrappedSMTInterpol = (SMTInterpol) mScript;
		mCustomNameId = 0;
		mAssertedTermsAreUnsat = false;
		mHandler = new TimeoutHandler(wrappedSMTInterpol.getTerminationRequest());
		mLogger = wrappedSMTInterpol.getLogger();
		mRandom = new Random(getRandomSeed());
		mRememberedAssertions = new ScopedArrayList<>();

		mInterpolationHeuristic = new EnumOption<>(HeuristicsType.RANDOM, true, HeuristicsType.class,
				"The Heuristic that is used to choose a minimal unsatisfiable subset/core for interpolant generation");
		mTolerance = new DoubleOption(0.1, true,
				"The tolerance value that is used by the SMALLESTAMONGWIDE and the WIDESTAMONGSMALL Heuristic.");
		mEnumerationTimeout = new LongOption(0, true, "The time that is invested into enumerating Muses");
		mHeuristicTimeout = new LongOption(0, true,
				"The time that is invested into finding the best Mus according to the set Heuristic");
		mLogAdditionalInformation = new BooleanOption(false, true,
				"Whether additional information (e.g. of the enumeration) should be logged.");
	}

	private long getRandomSeed() {
		return ((BigInteger) getOption(SMTLIBConstants.RANDOM_SEED)).longValue();
	}

	private long getEnumerationTimeout() {
		return ((BigInteger) getOption(MusOptions.ENUMERATION_TIMEOUT)).longValue();
	}

	private long getHeuristicTimeout() {
		return ((BigInteger) getOption(MusOptions.HEURISTIC_TIMEOUT)).longValue();
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
	 * This method first enumerates MUSes (with the ReMus algorithm) of the current asserted terms, then it applies a
	 * heuristic for choosing a MUS amongst them. Lastly, the proof of unsatisfiability of the chosen MUS is used to
	 * generate the Sequence of Interpolants that is returned. The enumeration of Muses, the heuristic and
	 * getInterpolants use different timeouts, respectively. If the timeout for the enumeration is exceeded, it returns
	 * the muses found so far. If the timeout for the heuristic is exceeded, it returns the best mus found so far wrt.
	 * the heuristic. If the timeout for generating the interpolant is exceeded, or the timeout for the enumeration is
	 * exceeded, before any MUSes could be produced, an SMTLIBException is thrown.
	 *
	 * OPTIONS: To set the used heuristic, use {@link #setOption(String, Object)} with the
	 * {@link MusOptions#INTERPOLATION_HEURISTIC} key and the respective {@link HeuristicsType} value. If you choose
	 * {@link HeuristicsType#SMALLESTAMONGWIDE} or {@link HeuristicsType#WIDESTAMONGSMALL}, you may also want to specify
	 * the value for the key {@link MusOptions#TOLERANCE} (for information about the tolerance, see
	 * {@link Heuristics#chooseWidestAmongSmallMuses(ArrayList, double, Random, TerminationRequest)} or
	 * {@link Heuristics#chooseSmallestAmongWideMuses(ArrayList, double, Random, TerminationRequest)}. To set the
	 * timeout for the enumeration, the heuristic or the Interpolation, call {@link #setOption(String, Object)} with the
	 * keys {@link MusOptions#ENUMERATION_TIMEOUT}, {@link MusOptions#HEURISTIC_TIMEOUT},
	 * {@link SMTInterpolOptions#TIMEOUT} respectively.
	 *
	 * This method is only available if proof production is enabled To enable proof production, call
	 * setOption(":produce-proofs",true).
	 */
	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree) {
		if (!mAssertedTermsAreUnsat) {
			throw new SMTLIBException(
					"Asserted terms must be determined to be unsatisfiable before an interpolant can be generated. Call checkSat to determine satisfiability.");
		} else if (!((boolean) getOption(SMTLIBConstants.PRODUCE_PROOFS))) {
			throw new SMTLIBException("Proof production must be enabled (you can do this via setOption).");
		}

		final long timeoutForReMus = getEnumerationTimeout();
		final long timeoutForHeuristic = getHeuristicTimeout();

		if (timeoutForReMus > 0) {
			mHandler.setTimeout(timeoutForReMus);
		}
		final ArrayList<MusContainer> muses = executeReMus();

		if (muses.isEmpty()) {
			throw new SMTLIBException("Timeout for ReMus exceeded before any muses could be found.");
		}

		if (mLogAdditionalInformation.getValue() == true) {
			String value;
			if (timeoutForReMus <= 0) {
				value = "Unlimited (no timeout set)";
			}else {
				value = Long.toString(timeoutForReMus);
			}
			mLogger.fatal("Timeout: " + value);
			mLogger.fatal("Number of enumerated Muses: " + muses.size());
			final long timeLeft = mHandler.timeLeft();
			if (timeLeft <= 0) {
				value = "0";
			}else if (timeLeft == Long.MAX_VALUE) {
				value = "Unlimited (no timeout set)";
			}else {
				value = Long.toString(timeLeft);
			}
			mLogger.fatal("Time left for enumeration: " + value);
		}
		mHandler.clearTimeout();

		if (timeoutForHeuristic > 0) {
			mHandler.setTimeout(timeoutForHeuristic);
		}
		final MusContainer chosenMus = chooseMusAccordingToHeuristic(muses, mHandler);
		mHandler.clearTimeout();

		final Term[] sequenceOfInterpolants = getInterpolants(partition, startOfSubtree, chosenMus.getProof());
		return sequenceOfInterpolants;
	}

	/**
	 * First, uses the ReMUS algorithm to enumerate MUSes of the set of asserted Terms. Then, it searches for the best
	 * MUS according to the chosen heuristic. If the first timeout is exceeded, the enumeration stops and the heuristic
	 * is applied to the MUSes found so far. If the second timeout is exceeded, the best MUS that has been found so far
	 * is returned. If ReMUS could not find any MUS in the given time, an arbitrary unsat core (i.e., the unsat core of
	 * the wrapped script) is returned, which is not necessarily minimal wrt. satisfiability. Every step (enumeration,
	 * heuristic, getUnsatCore of the wrapped script) has its own timeout.
	 *
	 * OPTIONS: To set the used heuristic, use {@link #setOption(String, Object)} with the
	 * {@link MusOptions#INTERPOLATION_HEURISTIC} key and the respective {@link HeuristicsType} value. If you choose
	 * {@link HeuristicsType#SMALLESTAMONGWIDE} or {@link HeuristicsType#WIDESTAMONGSMALL}, you may also want to specify
	 * the value for the key {@link MusOptions#TOLERANCE} (for information about the tolerance, see
	 * {@link Heuristics#chooseWidestAmongSmallMuses(ArrayList, double, Random, TerminationRequest)} or
	 * {@link Heuristics#chooseSmallestAmongWideMuses(ArrayList, double, Random, TerminationRequest)}. To set the
	 * timeout for the enumeration, the heuristic or the getUnsatCore of the wrapped script, call
	 * {@link #setOption(String, Object)} with the keys {@link MusOptions#ENUMERATION_TIMEOUT},
	 * {@link MusOptions#HEURISTIC_TIMEOUT}, {@link SMTInterpolOptions#TIMEOUT} respectively.
	 *
	 * This method is only available if proof production and unsat core production is enabled To enable proof
	 * production, call setOption(":produce-proofs",true). To enable unsat core production, call
	 * setOption(":produce-unsat-cores", true).
	 */
	@Override
	public Term[] getUnsatCore() {
		if (!mAssertedTermsAreUnsat) {
			throw new SMTLIBException(
					"Asserted Terms must be determined Unsat to return an unsat core. Call checkSat to determine satisfiability.");
		} else if (!((boolean) getOption(SMTLIBConstants.PRODUCE_UNSAT_CORES))) {
			throw new SMTLIBException("Unsat core production must be enabled (you can do this via setOption).");
		} else if (!((boolean) getOption(SMTLIBConstants.PRODUCE_PROOFS))) {
			throw new SMTLIBException("Proof production must be enabled (you can do this via setOption).");
		}

		final Term[] alternativeUnsatCore = mScript.getUnsatCore();
		final Translator translator = new Translator();

		final long timeoutForReMus = getEnumerationTimeout();
		final long timeoutForHeuristic = getHeuristicTimeout();

		if (timeoutForReMus > 0) {
			mHandler.setTimeout(timeoutForReMus);
		}
		final ArrayList<MusContainer> muses = executeReMus(translator);

		if (muses.isEmpty()) {
			return alternativeUnsatCore;
		}

		if (mLogAdditionalInformation.getValue() == true) {
			String value;
			if (timeoutForReMus <= 0) {
				value = "Unlimited (no timeout set)";
			}else {
				value = Long.toString(timeoutForReMus);
			}
			mLogger.fatal("Timeout: " + value);
			mLogger.fatal("Number of enumerated Muses: " + muses.size());
			final long timeLeft = mHandler.timeLeft();
			if (timeLeft <= 0) {
				value = "0";
			}else if (timeLeft == Long.MAX_VALUE) {
				value = "Unlimited (no timeout set)";
			}else {
				value = Long.toString(timeLeft);
			}
			mLogger.fatal("Time left for enumeration: " + value);
		}
		mHandler.clearTimeout();

		if (timeoutForHeuristic > 0) {
			mHandler.setTimeout(timeoutForHeuristic);
		}
		final MusContainer chosenMus = chooseMusAccordingToHeuristic(muses, mHandler);
		mHandler.clearTimeout();

		return translator.translateToTerms(chosenMus.getMus());
	}

	/**
	 * Executes the ReMus algorithm on the currently asserted Terms, with the internal TerminationRequest. If
	 * termination is requested, all MUSes that have been found so far are returned.
	 */
	private ArrayList<MusContainer> executeReMus() {
		final Translator translator = new Translator();
		return executeReMus(translator);
	}

	private ArrayList<MusContainer> executeReMus(final Translator translator) {
		if (translator.getNumberOfConstraints() != 0) {
			throw new SMTLIBException("Translator must be new.");
		}

		final TimeoutHandler handlerForReMus = new TimeoutHandler(mHandler);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), handlerForReMus);
		final Map<String, Object> remusOptions = createSMTInterpolOptionsForReMus();
		final SMTInterpol smtInterpol = (SMTInterpol) mScript;
		final TerminationRequest previousTerminationRequest = smtInterpol.getTerminationRequest();
		smtInterpol.setTerminationRequest(handlerForReMus);
		final Script scriptForReMus = new SMTInterpol((SMTInterpol) mScript, remusOptions, CopyMode.CURRENT_VALUE);

		scriptForReMus.push(1);

		registerTermsForEnumeration(mRememberedAssertions, translator, engine, scriptForReMus);
		resetCustomNameId();

		final UnexploredMap unexploredMap = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(scriptForReMus, translator);
		final int nrOfConstraints = solver.getNumberOfConstraints();
		final BitSet workingSet = new BitSet(nrOfConstraints);
		workingSet.flip(0, nrOfConstraints);

		final ReMus remus = new ReMus(solver, unexploredMap, workingSet, handlerForReMus, 0, mRandom);
		final ArrayList<MusContainer> muses;
		if (mInterpolationHeuristic.getValue() == HeuristicsType.FIRST) {
			muses = new ArrayList<>();
			if (remus.hasNext()) {
				muses.add(remus.next());
			}
		} else {
			muses = remus.enumerate();
		}
		remus.resetSolver();

		scriptForReMus.pop(1);
		smtInterpol.setTerminationRequest(previousTerminationRequest);
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
		case FIRST:
			assert muses.size() == 1 : "In case of the FIRST heuristic, only one mus should have been enumerated.";
			chosenMus = muses.get(0);
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
		} else if (opt.equals(MusOptions.ENUMERATION_TIMEOUT)) {
			mEnumerationTimeout.set(value);
		} else if (opt.equals(MusOptions.HEURISTIC_TIMEOUT)) {
			mHeuristicTimeout.set(value);
		} else if (opt.equals(MusOptions.LOG_ADDITIONAL_INFORMATION)) {
			mLogAdditionalInformation.set(value);
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
		} else if (opt.equals(MusOptions.ENUMERATION_TIMEOUT)) {
			return mEnumerationTimeout.get();
		} else if (opt.equals(MusOptions.HEURISTIC_TIMEOUT)) {
			return mHeuristicTimeout.get();
		} else if (opt.equals(MusOptions.LOG_ADDITIONAL_INFORMATION)) {
			return mLogAdditionalInformation.getValue();
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
		mEnumerationTimeout.reset();
		mHeuristicTimeout.reset();
		mLogAdditionalInformation.reset();
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
