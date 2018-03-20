/*
 * Copyright (C) 2018 University of Freiburg
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

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;

/**
 * Manage EUTerms. That is, decide if a term is essentially uninterpreted (i.e. ground or variables appear only as
 * arguments of uninterpreted function or predicate symbols), and build EUTerms in a nonrecursive way.
 * 
 * @author Tanja Schindler
 *
 */
public class EUTermManager extends NonRecursive {

	private final QuantifierTheory mQuantTheory;
	private final Clausifier mClausifier;

	/**
	 * The EUTerms built so far.
	 */
	private Map<Term, EUTerm> mEUTerms;
	/**
	 * Map from an EUTerm to all of its sub-EUTerms (including the term itself). At the moment, this is only initialized
	 * when needed. (We might not need it if a quantified EUTerm is turned into a ground EUTerm by DER.)
	 */
	private Map<EUTerm, Set<EUTerm>> mEUSubTerms;

	EUTermManager(final QuantifierTheory quantTheory) {
		mQuantTheory = quantTheory;
		mClausifier = quantTheory.getClausifier();
		mEUTerms = new HashMap<Term, EUTerm>();
	}

	/**
	 * Build an EUTerm for a given term if it is supported, i.e. if it is ground or all variables appear as arguments of
	 * uninterpreted function or predicate symbols only.
	 * 
	 * @param term
	 *            the term that is checked and transformed into an EUTerm.
	 * @param source
	 *            the source partition of the term.
	 * @return an EUTerm if the term is an essentially uninterpreted term. Throws an exception otherwise.
	 */
	public EUTerm getEUTerm(final Term term, final SourceAnnotation source) {
		if (mEUTerms.containsKey(term)) {
			return mEUTerms.get(term);
		} else {
			run(new EUTermBuilder(term, source));
			return mEUTerms.get(term);
		}
	}

	/**
	 * Compute all sub-EUTerms for a given EUTerm.
	 * 
	 * @param euTerm
	 *            the EUTerm which the sub-EUTerms are computed for.
	 * @return the set of EUTerms that are subterms of the given term (including the term itself).
	 */
	public Set<EUTerm> getSubEUTerms(final EUTerm euTerm) {
		if (mEUSubTerms == null) {
			mEUSubTerms = new HashMap<EUTerm, Set<EUTerm>>();
		}
		if (!mEUSubTerms.containsKey(euTerm)) {
			run(new ComputeSubEUTerms(euTerm));
		}
		return mEUSubTerms.get(euTerm);
	}

	private class EUTermBuilder implements Walker {

		private final Term mTerm;
		private final SourceAnnotation mSource;

		EUTermBuilder(final Term term, final SourceAnnotation source) {
			mTerm = term;
			mSource = source;
		}

		@Override
		public void walk(final NonRecursive engine) {
			if (mEUTerms.containsKey(mTerm)) {
				return;
			}
			if (mTerm.getFreeVars().length == 0) {
				buildGroundTerm(mTerm, mSource);
			} else if (mTerm instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) mTerm;
				if (!appTerm.getFunction().isIntern()) {
					enqueueWalker(new QuantAppTermBuilder(mTerm));
					for (Term arg : appTerm.getParameters()) {
						if (!(arg instanceof TermVariable)) {
							// If the parameter is not a TermVariable, it must be an EUTerm.
							enqueueWalker(new EUTermBuilder(arg, mSource));
						}
					}
				} else {
					final SMTAffineTerm affineTerm = SMTAffineTerm.create(mTerm);
					enqueueWalker(new QuantAffineTermBuilder(mTerm, affineTerm));
					for (Term summand : affineTerm.getSummands().keySet()) {
						enqueueWalker(new EUTermBuilder(summand, mSource));
					}
				}
			} else {
				throw new UnsupportedOperationException("Not an essentially uninterpreted term: " + mTerm);
			}
		}
	}

	private void buildGroundTerm(final Term term, final SourceAnnotation source) {
		assert term.getFreeVars().length == 0;
		if (!mEUTerms.containsKey(term)) {
			final SharedTerm shared = mClausifier.getSharedTerm(term, source);
			final GroundTerm ground = new GroundTerm(mClausifier, term, shared);
			mEUTerms.put(term, ground);
		}
	}

	private class QuantAppTermBuilder implements Walker {
		private final Term mTerm;

		QuantAppTermBuilder(final Term term) {
			mTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			assert mTerm instanceof ApplicationTerm;
			final ApplicationTerm appTerm = (ApplicationTerm) mTerm;
			final FunctionSymbol func = appTerm.getFunction();
			final Term[] args = appTerm.getParameters();
			QuantAppArg[] quantArgs = new QuantAppArg[args.length];
			for (int i = 0; i < args.length; i++) {
				final QuantAppArg arg;
				if (args[i] instanceof TermVariable) {
					arg = new QuantAppArg((TermVariable) args[i]);
				} else {
					// args that are not TermVariables have been checked, and corresponding EUTerms have been built.
					arg = new QuantAppArg(mEUTerms.get(args[i]));
				}
				quantArgs[i] = arg;
			}
			final QuantAppTerm quantAppTerm = new QuantAppTerm(mClausifier, mTerm, func, quantArgs);
			mEUTerms.put(mTerm, quantAppTerm);
		}
	}

	private class QuantAffineTermBuilder implements Walker {
		private final Term mTerm;
		private final SMTAffineTerm mAffine;

		QuantAffineTermBuilder(final Term term, final SMTAffineTerm affine) {
			mTerm = term;
			mAffine = affine;
		}

		@Override
		public void walk(final NonRecursive engine) {
			Map<Term, Rational> summands = mAffine.getSummands();
			Map<EUTerm, Rational> euSummands = new HashMap<EUTerm, Rational>();
			for (Term summand : summands.keySet()) {
				final Rational coeff = summands.get(summand);
				final EUTerm euTerm = mEUTerms.get(summand);
				euSummands.put(euTerm, coeff);
			}
			final QuantAffineTerm quantAffineTerm =
					new QuantAffineTerm(mClausifier, mTerm, euSummands, mAffine.getConstant());
			mEUTerms.put(mTerm, quantAffineTerm);
		}
	}

	private class ComputeSubEUTerms implements Walker {
		private final EUTerm mTerm;

		ComputeSubEUTerms(final EUTerm euTerm) {
			mTerm = euTerm;
		}

		@Override
		public void walk(final NonRecursive engine) {
			if (!mEUSubTerms.containsKey(mTerm)) {
				if (mTerm instanceof GroundTerm) {
					mEUSubTerms.put(mTerm, Collections.singleton(mTerm));
				} else if (mTerm instanceof QuantAppTerm) {
					enqueueWalker(new CollectSubEUTerms(mTerm));
					for (final QuantAppArg arg : ((QuantAppTerm) mTerm).getArgs()) {
						if (!arg.isVar() && !mEUSubTerms.containsKey(arg.getEUTerm())) {
							enqueueWalker(new ComputeSubEUTerms(arg.getEUTerm()));
						}
					}
				} else if (mTerm instanceof QuantAffineTerm) {
					enqueueWalker(new CollectSubEUTerms(mTerm));
					for (final EUTerm sub : ((QuantAffineTerm) mTerm).getSummands().keySet()) {
						if (!mEUSubTerms.containsKey(sub)) {
							enqueueWalker(new ComputeSubEUTerms(sub));
						}
					}
				}
			}
		}
	}

	private class CollectSubEUTerms implements Walker {
		private final EUTerm mTerm;

		CollectSubEUTerms(final EUTerm euTerm) {
			mTerm = euTerm;
		}

		@Override
		public void walk(final NonRecursive engine) {
			Set<EUTerm> subTerms = new HashSet<EUTerm>();
			subTerms.add(mTerm);
			if (mTerm instanceof QuantAppTerm) {
				for (final QuantAppArg arg : ((QuantAppTerm) mTerm).getArgs()) {
					if (!arg.isVar()) {
						final EUTerm euArg = arg.getEUTerm();
						assert mEUSubTerms.containsKey(euArg);
						subTerms.addAll(mEUSubTerms.get(euArg));
					}
				}
			} else {
				assert mTerm instanceof QuantAffineTerm;
				for (final EUTerm sub : ((QuantAffineTerm) mTerm).getSummands().keySet()) {
					assert mEUSubTerms.containsKey(sub);
					subTerms.addAll(mEUSubTerms.get(sub));
				}
			}
			mEUSubTerms.put(mTerm, subTerms);
		}
	}
}
