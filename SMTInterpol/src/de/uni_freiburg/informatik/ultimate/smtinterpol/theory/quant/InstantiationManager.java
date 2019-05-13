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

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClauseState;
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
		for (QuantClause quantClause : mQuantTheory.getQuantClauses()) {
			if (quantClause.getState() == EprClauseState.Fulfilled) {
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
		for (QuantClause quantClause : mQuantTheory.getQuantClauses()) {
			if (quantClause.getState() == EprClauseState.Fulfilled) {
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
				if (mClausifier.getEngine().isTerminationRequested())
					return Collections.emptySet();
				if (quantClause.getInterestingTerms()[i].isEmpty()) {
					final SharedTerm[] newSub = Arrays.copyOf(oldSub, oldSub.length);
					newSub[i] = null; // TODO Add lambda!
				} else {
					for (final SharedTerm ground : quantClause.getInterestingTerms()[i].values()) {
						final SharedTerm[] newSub = Arrays.copyOf(oldSub, oldSub.length);
						newSub[i] = ground;
						partialSubs.add(newSub);
					}
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
				assert quantClause.getState() == EprClauseState.Fulfilled;
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

		// Check quantified literals. TODO Where do we check for trivially true or false literals?
		for (QuantLiteral quantLit : quantClause.getQuantLits()) {
			InstanceValue litValue = InstanceValue.ONE_UNDEF;
			final boolean isNeg = quantLit.isNegated();
			final QuantLiteral atom = quantLit.getAtom();
			if (atom instanceof QuantEquality) {
				final QuantEquality eq = (QuantEquality) atom;
				final SharedTerm left = eq.getLhs() instanceof TermVariable ? 
						instantiation[quantClause.getVarIndex((TermVariable) eq.getLhs())]
						: findEquivalentShared(eq.getLhs(), quantClause.getSource(),
								quantClause.getVars(), instantiation);
				final SharedTerm right = eq.getRhs() instanceof TermVariable
						? instantiation[quantClause.getVarIndex((TermVariable) eq.getRhs())]
						: findEquivalentShared(eq.getRhs(), quantClause.getSource(),
								quantClause.getVars(), instantiation);
				if (left == null || right == null) {
					litValue = InstanceValue.ONE_UNDEF;
				} else {
					litValue = evaluateEquality(left, right);
				}
				// TODO What about arithmetic equalities? evaluateEquality treats them, but only if we have shared terms
				// for left and right.
			} else {
				final QuantBoundConstraint ineq = (QuantBoundConstraint) atom;
				final SMTAffineTerm lhs = findEquivalentShared(ineq.getAffineTerm(), quantClause.getSource(),
						quantClause.getVars(), instantiation);
				if (lhs == null) {
					litValue = InstanceValue.ONE_UNDEF;
				} else {
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

	/**
	 * For a given EUTerm and an instantiation, find an equivalent SharedTerm.
	 * 
	 * TODO Nonrecursive.
	 *
	 * @param euTerm
	 *            The EUTerm which we search an equivalent SharedTerm for.
	 * @param vars
	 *            The variables in the clause of this EUTerm.
	 * @param instantiation
	 *            The ground terms that should be instantiated for the variables.
	 * @return a SharedTerm equivalent to the instance of the given EUTerm if it exists, null otherwise.
	 */
	private SharedTerm findEquivalentShared(final Term term, final SourceAnnotation source,
			final TermVariable[] vars,
			final SharedTerm[] instantiation) {
		if (term.getFreeVars().length == 0) {
			return mClausifier.getSharedTerm(term, source);
		} else {
			assert term instanceof ApplicationTerm;
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol func = appTerm.getFunction();
			if (!func.isInterpreted()) {
				final Term [] args = appTerm.getParameters();
				final Term[] instArgs = new Term[args.length];
				for (int i = 0; i < args.length; i++) {
					if (args[i] instanceof TermVariable) {
						instArgs[i] = instantiation[Arrays.asList(vars).indexOf((TermVariable) args[i])].getTerm();
					} else {
						final SharedTerm sharedArg =
								findEquivalentShared(args[i], source, vars, instantiation);
						if (sharedArg == null) {
							return null;
						}
						instArgs[i] = sharedArg.getTerm();
					}
				}
				final Term instAppTerm = mClausifier.getTheory().term(func, instArgs);
				final CCTerm ccTermRep = mQuantTheory.getCClosure().getCCTermRep(instAppTerm);
				if (ccTermRep != null) {
					if (ccTermRep.getSharedTerm() != null) {
						return ccTermRep.getSharedTerm();
					} else {
						return ccTermRep.getFlatTerm();
					}
				} else {
					return null;
				}
			} else {
				// TODO "+", "*", "-". What about select etc.?
				return null;
			}
		}
	}

	private SMTAffineTerm findEquivalentShared(final SMTAffineTerm smtAff, final SourceAnnotation source,
			final TermVariable[] vars, final SharedTerm[] instantiation) {
		// TODO
		return null;
	}

	/**
	 * Determine the value that an equality literal between two given terms would have.
	 *
	 * TODO Should this do the simplification for trivially false/true literals?
	 *
	 * @param left
	 *            The left side of the equality.
	 * @param right
	 *            The right side of the equality.
	 * @return Value True if the two terms are in the same congruence class, False if they are definitely distinct,
	 *         Undef else.
	 */
	private InstanceValue evaluateEquality(final SharedTerm left, final SharedTerm right) {
		final CCTerm leftCC = left.getCCTerm();
		final CCTerm rightCC = right.getCCTerm();
		if (leftCC != null && rightCC != null) {
			if (mQuantTheory.getCClosure().isEqSet(leftCC, rightCC)) {
				return InstanceValue.TRUE;
			} else if (mQuantTheory.getCClosure().isDiseqSet(leftCC, rightCC)) {
				return InstanceValue.FALSE;
			}
		} else {
			final SMTAffineTerm smtAff = new SMTAffineTerm(left.getTerm());
			smtAff.add(Rational.MONE, right.getTerm());
			final InfinitesimalNumber upperBound = mQuantTheory.mLinArSolve.getUpperBound(mClausifier, smtAff);
			smtAff.negate();
			final InfinitesimalNumber lowerBound = mQuantTheory.mLinArSolve.getUpperBound(mClausifier, smtAff);
			if (upperBound.lesseq(InfinitesimalNumber.ZERO) && lowerBound.lesseq(InfinitesimalNumber.ZERO)) {
				return InstanceValue.TRUE;
			} else if (!upperBound.isInfinity() && !upperBound.lesseq(InfinitesimalNumber.ZERO)
					|| !lowerBound.isInfinity() && !lowerBound.lesseq(InfinitesimalNumber.ZERO)) {
				return InstanceValue.FALSE;
			}
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
