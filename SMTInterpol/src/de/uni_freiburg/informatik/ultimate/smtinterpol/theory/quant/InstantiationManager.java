/*
 * Copyright (C) 2019 University of Freiburg
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
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitesimalNumber;

/**
 * This class takes care of clause, literal and term instantiation.
 *
 * Literals and clauses are only created if necessary, in particular, false literals as well as clauses that would
 * contain true literals are not created.
 *
 * @author Tanja Schindler
 *
 */
public class InstantiationManager {

	private final Clausifier mClausifier;
	private final QuantifierTheory mQuantTheory;

	public InstantiationManager(Clausifier clausifier, QuantifierTheory quantTheory) {
		mClausifier = clausifier;
		mQuantTheory = quantTheory;
	}

	/**
	 * Find all instances of clauses that would be a conflict or unit clause if the corresponding theories had known the
	 * literals at creation of the instance.
	 *
	 * @return A Set of potentially conflicting and unit instances.
	 */
	public Set<List<Literal>> findConflictAndUnitInstances() {
		final Set<List<Literal>> conflictAndUnitClauses = new LinkedHashSet<>();
		// New Quant Clauses may be added when new instances are computed (e.g. axioms for ite terms)
		final List<QuantClause> currentQuantClauses = new ArrayList<>();
		currentQuantClauses.addAll(mQuantTheory.getQuantClauses());
		for (QuantClause quantClause : currentQuantClauses) {
			if (quantClause.getNumCurrentTrueLits() > 0) {
				continue;
			}
			final Set<SharedTerm[]> allInstantiations = computeAllInstantiations(quantClause);
			for (SharedTerm[] inst : allInstantiations) {
				if (mClausifier.getEngine().isTerminationRequested())
					return conflictAndUnitClauses;
				final InstanceValue clauseValue = evaluateClauseInstance(quantClause, inst);
				if (clauseValue != InstanceValue.TRUE) {
					final Term[] termSubs = new Term[inst.length];
					for (int i = 0; i < inst.length; i++) {
						termSubs[i] = inst[i].getTerm();
					}
					final Literal[] instLits = computeClauseInstance(quantClause, termSubs);
					if (instLits != null) {
						conflictAndUnitClauses.add(Arrays.asList(instLits));
						// quantClause.addInstance(inst);
					}
				}
			}
		}
		return conflictAndUnitClauses;
	}

	/**
	 * In the final check, check if all interesting instantiations of all clauses lead to satisfied instances. As soon
	 * as an instance is found that is not yet satisfied, stop. The newly created literals will be decided by the ground
	 * theories next and may lead to new conflicts.
	 * 
	 * If an actual conflict is found, return it (TODO This should not happen, checkpoint should have found it).
	 * 
	 * @return an actual conflict clause, if it exists; null otherwise.
	 */
	public Clause instantiateAll() {
		final List<QuantClause> currentQuantClauses = new ArrayList<>();
		currentQuantClauses.addAll(mQuantTheory.getQuantClauses());
		for (QuantClause quantClause : currentQuantClauses) {
			if (quantClause.getNumCurrentTrueLits() > 0) {
				continue;
			}
			final Set<SharedTerm[]> allInstantiations = computeAllInstantiations(quantClause);

			outer: for (SharedTerm[] inst : allInstantiations) {
				if (mClausifier.getEngine().isTerminationRequested())
					return null;
				final Term[] termSubs = new Term[inst.length];
				for (int i = 0; i < inst.length; i++) {
					termSubs[i] = inst[i].getTerm();
				}
				final Literal[] instLits = computeClauseInstance(quantClause, termSubs);
				if (instLits != null) {
					boolean isConflict = true;
					for (Literal lit : instLits) {
						if (lit.getAtom().getDecideStatus() == lit) { // instance satisfied
							continue outer;
						}
						if (lit.getAtom().getDecideStatus() == null) {
							isConflict = false;
						}
					}
					if (isConflict) {
						// quantClause.addInstance(inst);
						return new Clause(instLits);
					} else { // a new not yet satisfied instance has been created
						return null;
					}
				}
			}
		}
		return null;
	}

	/**
	 * Compute all instantiations for a given clause.
	 *
	 * @return a Set containing interesting instantiations for the clause.
	 */
	private Set<SharedTerm[]> computeAllInstantiations(QuantClause quantClause) {
		Set<SharedTerm[]> allSubs = new LinkedHashSet<SharedTerm[]>();
		allSubs.add(new SharedTerm[quantClause.getVars().length]);
		for (int i = 0; i < quantClause.getVars().length; i++) {
			Set<SharedTerm[]> partialSubs = new LinkedHashSet<SharedTerm[]>();
			for (final SharedTerm[] oldSub : allSubs) {
				if (mClausifier.getEngine().isTerminationRequested()) {
					return Collections.emptySet();
				}
				assert !quantClause.getInterestingTerms()[i].isEmpty();
				for (final SharedTerm ground : quantClause.getInterestingTerms()[i].values()) {
					final SharedTerm[] newSub = Arrays.copyOf(oldSub, oldSub.length);
					newSub[i] = ground;
					partialSubs.add(newSub);
				}
			}
			allSubs.clear();
			allSubs.addAll(partialSubs);
		}
		// allSubs.removeAll(quantClause.getInstantiations());
		return allSubs;
	}

	/**
	 * Evaluate which value a potential instance of a given clause would have. We distinguish three values: FALSE if all
	 * literals would be false, ONE_UNDEF if all but one literal would be false and this one undefined, and TRUE for all
	 * other cases.
	 *
	 * @param quantClause
	 *            the quantified clause which we evaluate an instance for.
	 * @param instantiation
	 *            the ground terms to instantiate.
	 * @return the value of the potential instance.
	 */
	private InstanceValue evaluateClauseInstance(final QuantClause quantClause, final SharedTerm[] instantiation) {
		InstanceValue clauseValue = InstanceValue.FALSE;

		// Check ground literals first.
		for (Literal groundLit : quantClause.getGroundLits()) {
			if (groundLit.getAtom().getDecideStatus() == groundLit) {
				assert quantClause.getNumCurrentTrueLits() > 0;
				return InstanceValue.TRUE;
			} else if (groundLit.getAtom().getDecideStatus() == null) {
				clauseValue.combine(InstanceValue.ONE_UNDEF);
			} else {
				assert groundLit.getAtom().getDecideStatus() != groundLit;
			}
		}
		// Only check clauses where all or all but one ground literals are set.
		if (clauseValue == InstanceValue.TRUE) {
			return clauseValue;
		}

		// Check quantified literals. TODO: Use SubstitutionHelper
		final SharedTermFinder finder =
				new SharedTermFinder(quantClause.getSource(), quantClause.getVars(), instantiation);
		for (QuantLiteral quantLit : quantClause.getQuantLits()) {
			InstanceValue litValue = InstanceValue.ONE_UNDEF;
			final boolean isNeg = quantLit.isNegated();
			final QuantLiteral atom = quantLit.getAtom();
			if (atom instanceof QuantEquality) {
				final QuantEquality eq = (QuantEquality) atom;
				final SharedTerm left = finder.findEquivalentShared(eq.getLhs());
				final SharedTerm right = finder.findEquivalentShared(eq.getRhs());
				if (left != null && right != null) {
					litValue = evaluateCCEquality(left, right);
				}
				if (litValue == InstanceValue.ONE_UNDEF && eq.getLhs().getSort().isNumericSort()) {
					final SMTAffineTerm sum = new SMTAffineTerm(eq.getLhs());
					sum.add(Rational.MONE, eq.getRhs());
					final SMTAffineTerm groundAff = finder.findEquivalentAffine(sum);
					if (groundAff != null) {
						litValue = evaluateLAEquality(groundAff);
					}
				}
			} else {
				final QuantBoundConstraint ineq = (QuantBoundConstraint) atom;
				final SMTAffineTerm lhs = finder.findEquivalentAffine(ineq.getAffineTerm());
				if (lhs != null) {
					litValue = evaluateBoundConstraint(lhs);
				}
			}

			if (isNeg) {
				litValue = litValue.negate();
			}
			clauseValue = clauseValue.combine(litValue);
			if (clauseValue == InstanceValue.TRUE) {
				return InstanceValue.TRUE;
			}
		}
		return clauseValue;
	}

	/**
	 * Instantiate a clause with a given substitution.
	 *
	 * @param clause
	 *            a clause containing at least one quantified literal
	 * @param sigma
	 *            pairs of variable and ground term that is used to instantiate the corresponding variable.
	 *
	 * @return the set of ground literals, or null if the clause would be true.
	 */
	private Literal[] computeClauseInstance(final QuantClause clause, final Term[] termSubs) {
		final Map<TermVariable, Term> sigma = new LinkedHashMap<>();
		for (int i = 0; i < termSubs.length; i++) {
			sigma.put(clause.getVars()[i], termSubs[i]);
		}
		final SubstitutionHelper instHelper = new SubstitutionHelper(mQuantTheory, clause.getGroundLits(),
				clause.getQuantLits(), clause.getSource(), sigma);
		instHelper.substituteInClause();
		if (instHelper.getResultingClauseTerm() == mQuantTheory.getTheory().mTrue) {
			return null;
		} else {
			assert instHelper.getResultingQuantLits().length == 0;
			final Literal[] resultingLits = instHelper.getResultingGroundLits();
			return resultingLits;
		}
	}

	private class SharedTermFinder extends NonRecursive {
		private final SourceAnnotation mSource;
		private final List<TermVariable> mVars;
		private final List<SharedTerm> mInstantiation;
		private final Map<Term, SharedTerm> mSharedTerms;

		SharedTermFinder(final SourceAnnotation source, final TermVariable[] vars,
				final SharedTerm[] instantiation) {
			mSource = source;
			mVars = Arrays.asList(vars);
			mInstantiation = Arrays.asList(instantiation);
			mSharedTerms = new HashMap<>();
		}

		SharedTerm findEquivalentShared(final Term term) {
			enqueueWalker(new FindSharedTerm(term));
			run();
			return mSharedTerms.get(term);
		}

		SMTAffineTerm findEquivalentAffine(final SMTAffineTerm smtAff) {
			for (final Term smd : smtAff.getSummands().keySet()) {
				enqueueWalker(new FindSharedTerm(smd));
			}
			run();
			return buildEquivalentAffine(smtAff);
		}

		private SMTAffineTerm buildEquivalentAffine(final SMTAffineTerm smtAff) {
			final SMTAffineTerm instAff = new SMTAffineTerm();
			for (final Entry<Term, Rational> smd : smtAff.getSummands().entrySet()) {
				final SharedTerm inst = mSharedTerms.get(smd.getKey());
				if (inst == null) {
					return null;
				}
				instAff.add(smd.getValue(), inst.getTerm());
			}
			instAff.add(smtAff.getConstant());
			return instAff;
		}

		class FindSharedTerm implements Walker {
			private final Term mTerm;

			public FindSharedTerm(final Term term) {
				mTerm = term;
			}

			@Override
			public void walk(final NonRecursive engine) {
				if (!mSharedTerms.containsKey(mTerm)) {
					if (mTerm.getFreeVars().length == 0) {
						mSharedTerms.put(mTerm, mClausifier.getSharedTerm(mTerm, mSource));
					} else if (mTerm instanceof TermVariable) {
						mSharedTerms.put(mTerm, mInstantiation.get(mVars.indexOf(mTerm)));
					} else {
						assert mTerm instanceof ApplicationTerm;
						final ApplicationTerm appTerm = (ApplicationTerm) mTerm;
						final FunctionSymbol func = appTerm.getFunction();
						if (Clausifier.needCCTerm(func)) {
							final Term[] params = appTerm.getParameters();
							enqueueWalker(new FindSharedAppTerm(mTerm, func, params));
							for (final Term arg : params) {
								enqueueWalker(new FindSharedTerm(arg));
							}
						} else if (func.getName() == "+" || func.getName() == "*" || func.getName() == "-") {
							final SMTAffineTerm smtAff = new SMTAffineTerm(mTerm);
							enqueueWalker(new FindSharedAffine(mTerm, smtAff));
							for (final Term smd : smtAff.getSummands().keySet()) {
								enqueueWalker(new FindSharedTerm(smd));
							}
						}
					}
				}
			}
		}

		class FindSharedAppTerm implements Walker {
			private final Term mTerm;
			private final FunctionSymbol mFunc;
			private final Term[] mParams;

			public FindSharedAppTerm(final Term term, final FunctionSymbol func, final Term[] params) {
				mTerm = term;
				mFunc = func;
				mParams = params;
			}

			@Override
			public void walk(final NonRecursive engine) {
				final Term[] instArgs = new Term[mParams.length];
				for (int i = 0; i < mParams.length; i++) {
					final SharedTerm sharedArg = mSharedTerms.get(mParams[i]);
					if (sharedArg == null) {
						return;
					} else {
						instArgs[i] = sharedArg.getTerm();
					}
				}
				final Term instAppTerm = mClausifier.getTheory().term(mFunc, instArgs);
				final CCTerm ccTermRep = mQuantTheory.getCClosure().getCCTermRep(instAppTerm);
				if (ccTermRep != null) {
					mSharedTerms.put(mTerm,
							ccTermRep.getSharedTerm() != null ? ccTermRep.getSharedTerm() : ccTermRep.getFlatTerm());
				}
			}
		}

		class FindSharedAffine implements Walker {
			private final Term mTerm;
			private final SMTAffineTerm mSmtAff;

			FindSharedAffine(final Term term, final SMTAffineTerm smtAff) {
				mTerm = term;
				mSmtAff = smtAff;
			}

			@Override
			public void walk(final NonRecursive engine) {
				final SMTAffineTerm instAffine = buildEquivalentAffine(mSmtAff);
				if (instAffine != null) {
					final Term instTerm = instAffine.toTerm(mTerm.getSort());
					final CCTerm ccTermRep = mQuantTheory.getCClosure().getCCTermRep(instTerm);
					if (ccTermRep != null) {
						mSharedTerms.put(mTerm, ccTermRep.getSharedTerm() != null ? ccTermRep.getSharedTerm()
								: ccTermRep.getFlatTerm());
					}
				}
			}
		}
	}

	/**
	 * Determine the value that an equality literal between two given SharedTerm would have.
	 *
	 * @param left
	 *            The left side of the equality.
	 * @param right
	 *            The right side of the equality.
	 * @return Value True if the two terms are in the same congruence class, False if they are definitely distinct,
	 *         Undef else.
	 */
	private InstanceValue evaluateCCEquality(final SharedTerm left, final SharedTerm right) {
		final CCTerm leftCC = left.getCCTerm();
		final CCTerm rightCC = right.getCCTerm();
		if (leftCC != null && rightCC != null) {
			if (mQuantTheory.getCClosure().isEqSet(leftCC, rightCC)) {
				return InstanceValue.TRUE;
			} else if (mQuantTheory.getCClosure().isDiseqSet(leftCC, rightCC)) {
				return InstanceValue.FALSE;
			}
		}
		return InstanceValue.ONE_UNDEF;
	}

	private InstanceValue evaluateLAEquality(final SMTAffineTerm smtAff) {
		final InfinitesimalNumber upperBound = mQuantTheory.mLinArSolve.getUpperBound(mClausifier, smtAff);
		smtAff.negate();
		final InfinitesimalNumber lowerBound = mQuantTheory.mLinArSolve.getUpperBound(mClausifier, smtAff);
		if (upperBound.lesseq(InfinitesimalNumber.ZERO) && lowerBound.lesseq(InfinitesimalNumber.ZERO)) {
			return InstanceValue.TRUE;
		} else if (!upperBound.isInfinity() && !upperBound.lesseq(InfinitesimalNumber.ZERO)
				|| !lowerBound.isInfinity() && !lowerBound.lesseq(InfinitesimalNumber.ZERO)) {
			return InstanceValue.FALSE;
		}
		return InstanceValue.ONE_UNDEF;
	}

	/**
	 * Determine the value that a bound constraint "term <= 0" would have.
	 *
	 * @param affine
	 *            The linear term for a constraint "term <= 0".
	 * @return Value True if the term has an upper bound <= 0, False if -term has a lower bound < 0, or Undef otherwise.
	 */
	private InstanceValue evaluateBoundConstraint(final SMTAffineTerm affine) {
		final InfinitesimalNumber upperBound = mQuantTheory.mLinArSolve.getUpperBound(mClausifier, affine);
		if (upperBound.lesseq(InfinitesimalNumber.ZERO)) {
			return InstanceValue.TRUE;
		} else {
			affine.negate();
			final InfinitesimalNumber lowerBound = mQuantTheory.mLinArSolve.getUpperBound(mClausifier, affine);
			if (lowerBound.less(InfinitesimalNumber.ZERO)) {
				return InstanceValue.FALSE;
			} else {
				return InstanceValue.ONE_UNDEF;
			}
		}
	}

	private enum InstanceValue {
		TRUE, FALSE, ONE_UNDEF;

		private InstanceValue combine(InstanceValue other) {
			if (this == InstanceValue.TRUE) {
				return this;
			} else if (this == InstanceValue.FALSE) {
				return other;
			} else {
				if (other == InstanceValue.FALSE) {
					return this;
				} else { // Note: UNDEF + UNDEF = TRUE
					return InstanceValue.TRUE;
				}
			}
		}

		private InstanceValue negate() {
			if (this == TRUE) {
				return InstanceValue.FALSE;
			} else if (this == FALSE) {
				return InstanceValue.TRUE;
			} else {
				return InstanceValue.ONE_UNDEF;
			}
		}
	}
}
