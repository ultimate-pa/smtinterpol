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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.InstantiationManager.InstanceValue;

public class IterativeModelBasedInstantiation {

	private final QuantifierTheory mQuantTheory;
	private final PiecewiseConstantModel mModel;
	private final Comparator<Term> mComparator;

	private QuantClause mClause;
	private Map<TermVariable, List<Term>> mInterestingTermsSorted; // TODO per literal
	private Deque<Pair<Term[], BitSet>> mTodo;

	IterativeModelBasedInstantiation(final QuantifierTheory quantTheory, final PiecewiseConstantModel model) {
		mQuantTheory = quantTheory;
		mModel = model;
		mComparator = new Comparator<Term>() {
			private final SharedTermEvaluator mStEval = new SharedTermEvaluator(mQuantTheory.getClausifier());

			/**
			 * Compare two terms. Numeric terms are compared by their Rational model value. Non-numeric terms are
			 * compared by their term age. If the model values or term ages are equal, they are compared by their hash
			 * codes. A lambda is always the smallest term of its sort.
			 */
			@Override
			public int compare(final Term t1, final Term t2) {
				if (t1 == t2) {
					return 0;
				}
				assert t1.getSort() == t2.getSort();
				final boolean isLambda1 = mQuantTheory.isLambdaOrDefaultTerm(t1);
				final boolean isLambda2 = mQuantTheory.isLambdaOrDefaultTerm(t2);
				if (isLambda1) {
					return isLambda2 ? 0 : -1;
				} else if (isLambda2) {
					return 1;
				}
				if (t1.getSort().isNumericSort()) {
					final Rational val1 = mStEval.evaluate(t1, mQuantTheory.getTheory());
					final Rational val2 = mStEval.evaluate(t2, mQuantTheory.getTheory());
					final int diff = val1.compareTo(val2);
					if (diff != 0) {
						return diff;
					}
				} else {
					final int age1 = mQuantTheory.getInstantiationManager().getTermAge(t1);
					final int age2 = mQuantTheory.getInstantiationManager().getTermAge(t2);
					final int termAgeDiff = age1 - age2;
					if (termAgeDiff != 0) {
						return termAgeDiff;
					}
				}
				assert t1.hashCode() != t2.hashCode();
				return t1.hashCode() < t2.hashCode() ? -1 : 1;
			}
		};
	}

	Term[] findSomeNonSatSubstitution(final QuantClause clause, final Term[] startSubs) {
		assert clause != mClause || startSubs != null;
		if (clause != mClause) {
			mClause = clause;
			mInterestingTermsSorted = new HashMap<>();
			mTodo = new ArrayDeque<>();
		}
		if (startSubs == null) {
			final Term[] lambdaSubs = buildLambdaSubs();
			mTodo.add(new Pair<>(lambdaSubs, new BitSet()));
		} else {
			if (mTodo.isEmpty() || !containsQueueGreaterSubs(startSubs)) {
				/*
				 * Start with the next strictly greater substitutions that falsify some literal. As a literal needs not
				 * contain all variables, it may be that we cannot built such a substitution from it, therefore we
				 * iterate over the literals until we find such substitutions.
				 */
				for (int i = 0; i < mClause.getQuantLits().length; i++) {
					final Collection<Term[]> nextGreaterSubs =
							findSmallestStrictlyGreaterNonSatSubstitutions(startSubs, i);
					if (!nextGreaterSubs.isEmpty()) {
						for (final Term[] s : nextGreaterSubs) {
							final BitSet unsatLits = new BitSet();
							unsatLits.set(i);
							mTodo.add(new Pair<>(s, unsatLits));
						}
						break;
					}
				}
			}
		}
		while (!mTodo.isEmpty() && !mQuantTheory.getClausifier().getEngine().isTerminationRequested()) {
			final Pair<Term[], BitSet> cand = mTodo.remove();
			final Term[] subs = cand.getFirst();
			final int satLitPos = findSatisfiedLiteralPosition(subs, cand.getSecond());
			if (satLitPos == -1) {
				return subs;
			}
			final Collection<Term[]> nextCandSubs = findSmallestStrictlyGreaterNonSatSubstitutions(subs, satLitPos);
			for (final Term[] s : nextCandSubs) {
				final int unsatLitPos = satLitPos;
				addToQueue(s, unsatLitPos);
			}
		}
		return null;
	}

	/**
	 * Check if there exists a literal that is satisfied under the given substitution and return its position in the
	 * clause.
	 *
	 * Do not use this method for clauses where a ground literal is currently satisfied.
	 *
	 * @param subs
	 *            a substitution for the clause variables
	 * @param dropLits
	 *            the literals that are exempt from this search
	 * @return the position of a quantified literal that is satisfied under the given substitution, -1 if none is
	 *         (except maybe the literals removed by droplits).
	 */
	private int findSatisfiedLiteralPosition(final Term[] subs, final BitSet dropLits) {
		// Check existing clause instance
		final InstClause knownInst =
				mQuantTheory.getInstantiationManager().getClauseInstances(mClause).get(Arrays.asList(subs));
		if (knownInst != null) {
			final int numUndef = knownInst.countAndSetUndefLits();
			if (knownInst.isConflict()) {
				return -1;
			} else {
				assert numUndef == -1;
			}
		}
		// Check existing literal instances
		int numExistingInstances = 0;
		for (int i = 0; i < mClause.getQuantLits().length; i++) {
			if (!dropLits.get(i)) {
				final QuantLiteral lit = mClause.getQuantLits()[i];
				if (!mQuantTheory.getInstantiationManager().getLitInstances(lit).isEmpty()) {
					final List<Term> subsForVarLits = new ArrayList<>();
					for (final TermVariable v : lit.getTerm().getFreeVars()) {
						subsForVarLits.add(subs[mClause.getVarIndex(v)]);
					}
					final ILiteral inst =
							mQuantTheory.getInstantiationManager().getLitInstances(lit).get(subsForVarLits);
					if (inst != null) {
						numExistingInstances++;
					}
					if (inst == InstantiationManager.mTRUE) {
						return i;
					} else if (inst instanceof Literal) {
						final Literal instLit = (Literal) inst;
						if (instLit.getAtom().getDecideStatus() == instLit) {
							return i;
						}
					}
				}
			}
		}
		if (numExistingInstances == mClause.getQuantLits().length) {
			mQuantTheory.getLogger().warn(
					"QUANT: detected conflicting clause for which all literal instances exist but not clause instance.");
			return -1;
		}

		// Evaluate literals in the model
		final List<Term> subsList = Arrays.asList(subs);
		// Start with arithmetical literals if existing, they are evaluated easily in the final check.
		final BitSet isNonArithmetical = new BitSet();
		for (int i = 0; i < mClause.getQuantLits().length; i++) {
			if (!dropLits.get(i)) {
				final QuantLiteral l = mClause.getQuantLits()[i];
				if (l.isArithmetical()) {
					final InstanceValue val = mModel.evaluateArithmeticalLiteral(l, subsList);
					if (val == InstanceValue.TRUE) {
						return i;
					}
				} else {
					isNonArithmetical.set(i);
				}
			}
		}
		// Check the remaining literals
		for (int i = 0; i < mClause.getQuantLits().length; i++) {
			if (!dropLits.get(i) && isNonArithmetical.get(i)) {
				final InstanceValue litValue = mModel.evaluateLiteral(mClause.getQuantLits()[i], subsList);
				if (litValue == InstanceValue.TRUE) {
					return i;
				}
			}
		}
		return -1;
	}

	private List<Term[]> findSmallestStrictlyGreaterNonSatSubstitutions(final Term[] subs, final int litPos) {
		final QuantLiteral lit = mClause.getQuantLits()[litPos];

		final TermVariable[] litVars = lit.getTerm().getFreeVars();
		// first sort the interesting terms for the variables in the literal (if not in mInterestingTerms)
		for (final TermVariable v : litVars) {
			if (!mInterestingTermsSorted.containsKey(v)) {
				final int posInClause = mClause.getVarIndex(v);
				mInterestingTermsSorted.put(v, sortInterestingTermsByModelValue(mClause.getInterestingTerms()[posInClause].values()));
			}
		}

		// then build the next greater substitutions for which the literal is not satisfied
		final List<Term[]> nonSatSubs = new ArrayList<>();
		final List<Term[]> minimalSubs = new ArrayList<>();
		minimalSubs.add(subs);
		for (final TermVariable v : litVars) {
			final int posInClause = mClause.getVarIndex(v);
			final List<Term[]> oldMinimalSubs = new ArrayList<>();
			oldMinimalSubs.addAll(minimalSubs);
			for (final Term[] s : oldMinimalSubs) {
				if (mQuantTheory.getClausifier().getEngine().isTerminationRequested()) {
					return Collections.emptyList();
				}
				final List<Term> interesting = mInterestingTermsSorted.get(v);
				final Term currentSubs = s[posInClause];
				final int currentSubsPosInInteresting = interesting.indexOf(currentSubs);
				assert currentSubsPosInInteresting >= 0;
				for (int i = currentSubsPosInInteresting + 1; i < interesting.size(); i++) {
					final Term nextSubs = interesting.get(i);
					final Term[] newSubs = Arrays.copyOf(s, s.length);
					newSubs[posInClause] = nextSubs;
					if (v == litVars[litVars.length - 1] && containsSmallerOrEqualSubs(nonSatSubs, newSubs)) {
						break;
					}
					final InstanceValue val =
							lit.isArithmetical() ? mModel.evaluateArithmeticalLiteral(lit, Arrays.asList(newSubs))
									: mModel.evaluateLiteral(lit, Arrays.asList(newSubs));
							if (val == InstanceValue.FALSE) {
								nonSatSubs.add(newSubs);
								break;
							} else {
								minimalSubs.add(newSubs);
							}
				}
			}
		}
		return nonSatSubs;
	}

	private List<Term> sortInterestingTermsByModelValue(final Collection<Term> terms) {
		final List<Term> termList = new ArrayList<>();
		termList.addAll(terms);
		Collections.sort(termList, mComparator);
		return termList;
	}

	private Term[] buildLambdaSubs() {
		final Term[] lambdaSubs = new Term[mClause.getVars().length];
		for (int i = 0; i < mClause.getVars().length; i++) {
			lambdaSubs[i] = mQuantTheory.getLambdaOrDefaultTerm(mClause.getVars()[i].getSort());
		}
		return lambdaSubs;
	}

	private void addToQueue(final Term[] subs, final int unsatLitPos) {
		for (final Pair<Term[], BitSet> itm : mTodo) {
			final Term[] existingSubs = itm.getFirst();
			if (Arrays.equals(existingSubs, subs)) {
				itm.getSecond().set(unsatLitPos);
				return;
			}
			if (isSmallerOrEqual(existingSubs, subs)) {
				return;
			}
		}
		final BitSet unsatLits = new BitSet();
		unsatLits.set(unsatLitPos);
		mTodo.add(new Pair<>(subs, unsatLits));
	}

	private boolean containsQueueGreaterSubs(final Term[] subs) {
		for (final Pair<Term[], BitSet> itm : mTodo) {
			final Term[] existingSubs = itm.getFirst();
			if (!isSmallerOrEqual(existingSubs, subs)) {
				return true;
			}
		}
		return false;
	}

	private boolean containsSmallerOrEqualSubs(final Collection<Term[]> substitutions, final Term[] subs) {
		for (final Term[] s : substitutions) {
			if (isSmallerOrEqual(s, subs)) {
				return true;
			}
		}
		return false;
	}

	private boolean isSmallerOrEqual(final Term[] s1, final Term[] s2) {
		assert s1.length == s2.length;
		for (int i = 0; i < s1.length; i++) {
			if (mComparator.compare(s1[i], s2[i]) > 0) {
				return false;
			}
		}
		return true;
	}
}
