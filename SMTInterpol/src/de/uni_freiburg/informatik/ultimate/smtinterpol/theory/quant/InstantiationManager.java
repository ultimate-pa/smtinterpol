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
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitesimalNumber;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.dawg.Dawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.ematching.EMatching;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.ematching.EMatching.SubstitutionInfo;

/**
 * This class takes care of clause, literal and term instantiation.
 * 
 * Literals are pre-evaluated in order to create less false literals and clauses containing true literals.
 * 
 * TODO Rework methods that do almost the same.
 *
 * @author Tanja Schindler
 *
 */
public class InstantiationManager {

	private final Clausifier mClausifier;
	private final QuantifierTheory mQuantTheory;
	private final EMatching mEMatching;

	private final Map<QuantClause, Map<List<SharedTerm>, InstClause>> mClauseInstances;

	private final InstanceValue mDefaultValueForLitDawgs;
	private final InstanceValue[] mRelevantValuesForCheckpoint;

	public InstantiationManager(Clausifier clausifier, QuantifierTheory quantTheory) {
		mClausifier = clausifier;
		mQuantTheory = quantTheory;
		mEMatching = quantTheory.getEMatching();
		mClauseInstances = new HashMap<>();
		mDefaultValueForLitDawgs =
				mQuantTheory.mUseUnknownTermValueInDawgs ? InstanceValue.UNKNOWN_TERM : InstanceValue.ONE_UNDEF;
		mRelevantValuesForCheckpoint = mQuantTheory.mPropagateNewTerms
				? new InstanceValue[] { InstanceValue.FALSE, InstanceValue.ONE_UNDEF, InstanceValue.UNKNOWN_TERM }
				: new InstanceValue[] { InstanceValue.FALSE, InstanceValue.ONE_UNDEF };
	}

	/**
	 * Add the clause to the instance map.
	 * 
	 * @param qClause
	 *            the quantified clause.
	 */
	public void addClause(final QuantClause qClause) {
		mClauseInstances.put(qClause, new HashMap<>());
	}

	/**
	 * Reset the interesting terms for a variable.
	 */
	public void resetInterestingTerms() {
		for (final QuantClause qClause : mQuantTheory.getQuantClauses()) {
			qClause.clearInterestingTerms();
		}
	}

	/**
	 * Find all current instances of quant clauses that would be conflict or unit instances. This will actually compute
	 * the clause instances, i.e., it will create the ground literals.
	 * 
	 * @return the clause instances.
	 */
	public Set<InstClause> findConflictAndUnitInstancesWithEMatching() {
		final Set<InstClause> conflictAndUnitClauses = new LinkedHashSet<>();

		// New Quant Clauses may be added when new instances are computed (e.g. axioms for ite terms)
		final List<QuantClause> currentQuantClauses = new ArrayList<>();
		currentQuantClauses.addAll(mQuantTheory.getQuantClauses());

		for (final QuantClause qClause : currentQuantClauses) {
			if (mQuantTheory.getEngine().isTerminationRequested()) {
				return Collections.emptySet();
			}
			final Dawg<SharedTerm, InstanceValue> dawg = computeClauseDawg(qClause);
			final Collection<List<SharedTerm>> conflictOrUnitSubs = getConflictAndUnitSubsFromDawg(qClause, dawg);
			if (conflictOrUnitSubs != null) {
				for (final List<SharedTerm> subs : conflictOrUnitSubs) {
					if (mQuantTheory.getEngine().isTerminationRequested()) {
						return Collections.emptySet();
					}
					final InstClause inst = computeClauseInstance(qClause, subs);
					if (inst != null) {
						conflictAndUnitClauses.add(inst);
					}
				}
			}
		}
		return conflictAndUnitClauses;
	}

	/**
	 * Find all instances of clauses that would be a conflict or unit clause if the corresponding theories had known the
	 * literals at creation of the instance.
	 *
	 * @return A Set of potentially conflicting and unit instances.
	 */
	public Set<InstClause> findConflictAndUnitInstances() {
		final Set<InstClause> conflictAndUnitClauses = new LinkedHashSet<>();
		// New Quant Clauses may be added when new instances are computed (e.g. axioms for ite terms)
		final List<QuantClause> currentQuantClauses = new ArrayList<>();
		currentQuantClauses.addAll(mQuantTheory.getQuantClauses());
		for (QuantClause quantClause : currentQuantClauses) {
			if (quantClause.hasTrueGroundLits()) {
				continue;
			}
			final Set<List<SharedTerm>> allSubstitutions = computeAllSubstitutions(quantClause);
			for (List<SharedTerm> subs : allSubstitutions) {
				if (mClausifier.getEngine().isTerminationRequested())
					return Collections.emptySet();
				// TODO Don't evaluate existing instances
				final InstanceValue clauseValue = evaluateClauseInstance(quantClause, subs);
				if (clauseValue != InstanceValue.IRRELEVANT) {
					final InstClause inst = computeClauseInstance(quantClause, subs);
					if (inst != null) {
						conflictAndUnitClauses.add(inst);
					}
				}
			}
		}
		return conflictAndUnitClauses;
	}

	/**
	 * In the final check, check if all interesting substitutions of all clauses lead to satisfied instances. As soon as
	 * an instance is found that is not yet satisfied, stop. The newly created literals will be decided by the ground
	 * theories next and may lead to new conflicts.
	 * 
	 * If an actual conflict is found, return it.
	 * 
	 * @return an actual conflict clause, if it exists; null otherwise.
	 */
	public Clause instantiateSomeNotSat() {
		final List<Pair<QuantClause, List<SharedTerm>>> otherValueInstancesOnKnownTerms = new ArrayList<>();
		final List<Pair<QuantClause, List<SharedTerm>>> unitValueInstancesNewTerms = new ArrayList<>();
		final List<Pair<QuantClause, List<SharedTerm>>> otherValueInstancesNewTerms = new ArrayList<>();

		final List<QuantClause> currentQuantClauses = new ArrayList<>();
		currentQuantClauses.addAll(mQuantTheory.getQuantClauses());

		// First check if an existing instance leads to a conflict. TODO: checkpoint() should have detected it!
		for (final QuantClause qClause : currentQuantClauses) {
			assert mClauseInstances.containsKey(qClause);
			for (final Entry<List<SharedTerm>, InstClause> existingInst : mClauseInstances.get(qClause).entrySet()) {
				final InstClause instClause = existingInst.getValue();
				if (instClause != null) {
					final int numUndef = instClause.countAndSetUndefLits();
					assert numUndef == -1 || numUndef == 0;
					if (numUndef == 0) {
						mQuantTheory.getLogger().warn(
								"Conflict on existing clause instance hasn't been detected in checkpoint(): ",
								instClause);
						return instClause.toClause(mQuantTheory.getEngine().isProofGenerationEnabled());
					}
				}
			}
		}

		// If no existing instance lead to a conflict, check new instances.
		for (QuantClause quantClause : currentQuantClauses) {
			if (quantClause.hasTrueGroundLits()) {
				continue;
			}
			final Set<List<SharedTerm>> allSubstitutions = computeAllSubstitutions(quantClause);
			for (List<SharedTerm> subs : allSubstitutions) {
				if (mClausifier.getEngine().isTerminationRequested()) {
					return null;
				}
				if (mClauseInstances.containsKey(quantClause) && mClauseInstances.get(quantClause).containsKey(subs)) {
					continue; // Checked in the first loop over the quant clauses.
				}
				final Pair<InstanceValue, Boolean> candVal = evaluateNewClauseInstanceFinalCheck(quantClause, subs);
				if (candVal.getFirst() == InstanceValue.TRUE) {
					continue;
				} else if (candVal.getFirst() == InstanceValue.FALSE || candVal.getFirst() == InstanceValue.ONE_UNDEF) {
					// Always build conflict or unit clauses on known terms
					assert candVal.getSecond().booleanValue();
					final InstClause unitClause = computeClauseInstance(quantClause, subs);
					assert unitClause != null;
					final int numUndef = unitClause.countAndSetUndefLits();
					if (numUndef == 0) { // TODO Can this happen in final check? (At the moment, yes.)
						return unitClause.toClause(mQuantTheory.getEngine().isProofGenerationEnabled());
					} else if (numUndef > 0) {
						return null;
					}
				} else {
					final Pair<QuantClause, List<SharedTerm>> clauseSubsPair = new Pair<>(quantClause, subs);
					if (candVal.getFirst() == InstanceValue.UNKNOWN_TERM) {
						assert !candVal.getSecond().booleanValue();
						unitValueInstancesNewTerms.add(clauseSubsPair);
					} else {
						assert candVal.getFirst() == InstanceValue.OTHER;
						if (candVal.getSecond().booleanValue()) {
							otherValueInstancesOnKnownTerms.add(clauseSubsPair);
						} else {
							otherValueInstancesNewTerms.add(clauseSubsPair);
						}
					}
				}
			}
		}
		// If we haven't found a conflict instance or a unit instance on known terms, first check other non-sat
		// instances on known terms, then unit instances producing new terms, then other non-sat instances on new terms
		final List<Pair<QuantClause, List<SharedTerm>>> sortedInstances = new ArrayList<>();
		sortedInstances.addAll(otherValueInstancesOnKnownTerms);
		sortedInstances.addAll(unitValueInstancesNewTerms);
		sortedInstances.addAll(otherValueInstancesNewTerms);
		for (final Pair<QuantClause, List<SharedTerm>> cand : sortedInstances) {
			final InstClause inst = computeClauseInstance(cand.getFirst(), cand.getSecond());
			if (inst != null) {
				final int numUndef = inst.countAndSetUndefLits();
				if (numUndef == 0) {
					return inst.toClause(mQuantTheory.getEngine().isProofGenerationEnabled());
				} else if (numUndef > 0) {
					return null;
				}
			}
		}
		return null;
	}

	/**
	 * Get the default dawg for a given literal.
	 * 
	 * @param qLit
	 *            a quantified literal.
	 * @return a constant undef or unknown (according to options set) dawg of depth |clausevars|.
	 */
	private Dawg<SharedTerm, InstanceValue> getDefaultLiteralDawg(final QuantLiteral qLit) {
		return Dawg.createConst(qLit.mClause.getVars().length, mDefaultValueForLitDawgs);
	}

	/**
	 * Compute a clause dawg.
	 * 
	 * @param qClause
	 *            the quantified clause.
	 * @return the dawg that contains the evaluations of different potential instances.
	 */
	private Dawg<SharedTerm, InstanceValue> computeClauseDawg(final QuantClause qClause) {
		final Dawg<SharedTerm, InstanceValue> constIrrelDawg =
				Dawg.createConst(qClause.getVars().length, InstanceValue.IRRELEVANT);

		// Initialize clause value to false for correct combination.
		InstanceValue clauseValue = InstanceValue.FALSE;

		// Check ground literals first
		for (Literal groundLit : qClause.getGroundLits()) {
			if (groundLit.getAtom().getDecideStatus() == groundLit) {
				clauseValue = combineForCheckpoint(clauseValue, InstanceValue.TRUE);
			} else if (groundLit.getAtom().getDecideStatus() == groundLit.negate()) {
				clauseValue = combineForCheckpoint(clauseValue, InstanceValue.FALSE);
			} else {
				clauseValue = combineForCheckpoint(clauseValue, InstanceValue.ONE_UNDEF);
			}
			if (clauseValue == InstanceValue.IRRELEVANT) {
				break;
			}
		}

		// Create the partial clause dawg.
		final int length = qClause.getVars().length;
		Dawg<SharedTerm, InstanceValue> clauseDawg = Dawg.createConst(length, clauseValue);

		// Only check quant literals for clauses where all or all but one ground literals are false.
		if (clauseValue != InstanceValue.IRRELEVANT) {
			final BiFunction<InstanceValue, InstanceValue, InstanceValue> combinator =
					(v1, v2) -> combineForCheckpoint(v1, v2);
			final Collection<QuantLiteral> unknownLits = new ArrayList<>(qClause.getQuantLits().length);
			final Collection<QuantLiteral> arithLits = new ArrayList<>(qClause.getQuantLits().length);
			// First update and combine the literals that are not arithmetical
			for (final QuantLiteral qLit : qClause.getQuantLits()) {
				if (clauseDawg == constIrrelDawg) {
					break;
				}
				if (qLit.isArithmetical()) { // will be treated later
					arithLits.add(qLit);
				} else if (mEMatching.isUsingEmatching(qLit)) {
					Dawg<SharedTerm, InstanceValue> litDawg = getDefaultLiteralDawg(qLit);
					litDawg = computeEMatchingLitDawg(qLit);
					clauseDawg = clauseDawg.combine(litDawg, combinator);
				} else {
					unknownLits.add(qLit);
				}
			}
			if (clauseDawg != constIrrelDawg && !unknownLits.isEmpty()) {
				// Consider all substitutions where the partial clause Dawg is not already true
				for (final QuantLiteral lit : unknownLits) {
					if (clauseDawg == constIrrelDawg) {
						break;
					}
					clauseDawg = clauseDawg.mapWithKey((key, value) -> (value == InstanceValue.IRRELEVANT ? value
							: combineForCheckpoint(value, evaluateLitInstance(lit, key))));
				}
			}
			if (clauseDawg != constIrrelDawg && !arithLits.isEmpty()) {
				// Compute relevant terms from dawg and from bounds for arithmetical literals, update and combine dawgs.
				final SharedTerm[][] interestingSubsForArith =
						computeSubsForArithmetical(qClause, arithLits, clauseDawg);
				// Consider all substitutions where the partial clause Dawg is not already true
				for (final QuantLiteral arLit : arithLits) {
					if (clauseDawg == constIrrelDawg) {
						break;
					}
					final Dawg<SharedTerm, InstanceValue> litDawg = computeArithLitDawg(arLit, interestingSubsForArith);
					clauseDawg = clauseDawg.combine(litDawg, combinator);
				}
			}
		}
		return clauseDawg;
	}

	final InstanceValue combineForCheckpoint(InstanceValue first, InstanceValue second) {
		return (first.combine(second)).keepOnlyRelevant(mRelevantValuesForCheckpoint);
	}

	final boolean isUsedValueForCheckpoint(InstanceValue value) {
		if (value == InstanceValue.IRRELEVANT) {
			return true;
		}
		for (final InstanceValue relVal : mRelevantValuesForCheckpoint) {
			if (value == relVal) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Compute the evaluation dawg for a given literal handled by E-matching.
	 * 
	 * @param qLit
	 *            a quantified literal that is handled by E-matching.
	 * @return the evaluation dawg for the literal, of depth |clausevars|.
	 */
	private Dawg<SharedTerm, InstanceValue> computeEMatchingLitDawg(final QuantLiteral qLit) {
		assert mEMatching.isUsingEmatching(qLit);
		final Dawg<SharedTerm, SubstitutionInfo> atomSubsDawg = mEMatching.getSubstitutionInfos(qLit.getAtom());
		if (atomSubsDawg != null) {
			final Function<SubstitutionInfo, InstanceValue> evaluationMap =
					v1 -> evaluateLitForEMatchingSubsInfo(qLit, v1);
			return atomSubsDawg.map(evaluationMap);
		} else {
			return getDefaultLiteralDawg(qLit);
		}
	}

	/**
	 * Evaluate a literal for a given substitution.
	 * 
	 * @param qLit
	 *            a quantified literal.
	 * @param info
	 *            the substitution info, containing variable substitutions and equivalent CCTerms for EU terms in the
	 *            literal.
	 * @return the InstanceValue of the literal for the substitution.
	 */
	private InstanceValue evaluateLitForEMatchingSubsInfo(final QuantLiteral qLit, final SubstitutionInfo info) {
		final QuantLiteral qAtom = qLit.getAtom();
		if (info == mEMatching.getEmptySubs()) {
			if (mQuantTheory.mPropagateNewAux && !mQuantTheory.mPropagateNewTerms && qAtom instanceof QuantEquality) {
				if (QuantifiedTermInfo.isAuxApplication(((QuantEquality) qAtom).getLhs())) {
					return InstanceValue.ONE_UNDEF;
				}
			}
			return mDefaultValueForLitDawgs;
		}

		InstanceValue val;
		if (qAtom instanceof QuantBoundConstraint) {
			final Map<Term, SharedTerm> sharedForQuantSmds = buildSharedMapFromCCMap(info.getEquivalentCCTerms());
			val = evaluateBoundConstraintKnownShared((QuantBoundConstraint) qAtom, sharedForQuantSmds);
		} else {
			// First try if we can get an equality value in CC.
			final QuantEquality qEq = (QuantEquality) qAtom;
			val = evaluateCCEqualityKnownShared(qEq, info);

			// If the eq value is unknown in CC, and the terms are numeric, check for equality in LinAr.
			if ((val == InstanceValue.ONE_UNDEF || val == InstanceValue.UNKNOWN_TERM)
					&& qEq.getLhs().getSort().isNumericSort()) {
				final Map<Term, SharedTerm> sharedForQuantSmds = buildSharedMapFromCCMap(info.getEquivalentCCTerms());
				val = evaluateLAEqualityKnownShared(qEq, sharedForQuantSmds);
			}
		}

		if (qLit.isNegated()) {
			val = val.negate();
		}
		return val;
	}

	private InstanceValue evaluateLitInstance(final QuantLiteral quantLit, final List<SharedTerm> substitution) {
		InstanceValue litValue = mDefaultValueForLitDawgs;
		final boolean isNeg = quantLit.isNegated();
		final QuantLiteral atom = quantLit.getAtom();
		if (atom instanceof QuantEquality) {
			final QuantEquality eq = (QuantEquality) atom;
			litValue = evaluateCCEquality(eq, substitution);
			if ((litValue == InstanceValue.ONE_UNDEF || litValue == InstanceValue.UNKNOWN_TERM) && eq.getLhs().getSort().isNumericSort()) {
				litValue = evaluateLAEquality(eq, substitution);
			}
		} else {
			litValue = evaluateBoundConstraint((QuantBoundConstraint) atom, substitution);
		}

		if (isNeg) {
			litValue = litValue.negate();
		}
		return litValue;
	}

	/**
	 * Compute the literal evaluation dawg for arithmetical literals.
	 * 
	 * @param arLit
	 *            the arithmetical literal.
	 * @param interestingSubs
	 *            the potentially interesting substitutions for the variables in the clause.
	 * @return am evaluation dawg for the literal, its depth corresponds to the number of variables in the clause.
	 */
	private Dawg<SharedTerm, InstanceValue> computeArithLitDawg(final QuantLiteral arLit,
			final SharedTerm[][] interestingSubs) {
		final QuantLiteral qAtom = arLit.getAtom();
		final TermVariable[] varsInLit = qAtom.getTerm().getFreeVars();
		assert varsInLit.length == 1 || varsInLit.length == 2;

		TermVariable var = varsInLit[0];
		TermVariable otherVar = varsInLit.length == 2 ? varsInLit[1] : null;
		int varPosInClause = arLit.getClause().getVarIndex(varsInLit[0]);
		int firstVarPosInClause = otherVar == null ? varPosInClause : arLit.getClause().getVarIndex(varsInLit[1]);
		// the other variable position must be the smaller one according to the variable order in the clause
		if (otherVar != null && firstVarPosInClause > varPosInClause) {
			final int temp = varPosInClause;
			varPosInClause = firstVarPosInClause;
			firstVarPosInClause = temp;
			final TermVariable tempVar = var;
			var = otherVar;
			otherVar = tempVar;
		}

		final int nOuterLoops = otherVar == null ? 1 : interestingSubs[firstVarPosInClause].length;
		final Map<SharedTerm, Dawg<SharedTerm, InstanceValue>> transitionsFromOtherVar = new LinkedHashMap<>();

		final int remainderDawgLengthForVar = arLit.getClause().getVars().length - varPosInClause - 1;
		Dawg<SharedTerm, InstanceValue> remainderDawgAllVars = null;

		for (int i = 0; i < nOuterLoops; i++) {
			final SharedTerm otherSubs = otherVar != null ? interestingSubs[firstVarPosInClause][i] : null;

			final Map<SharedTerm, Dawg<SharedTerm, InstanceValue>> transitionsFromVar = new LinkedHashMap<>();
			for (final SharedTerm subs : interestingSubs[varPosInClause]) {
				InstanceValue val = InstanceValue.ONE_UNDEF;

				// Build substitution map.
				final Map<Term, SharedTerm> subsMap = new HashMap<>();
				subsMap.put(var, subs);
				if (otherVar != null) {
					subsMap.put(otherVar, otherSubs);
				}
				// Evaluate
				if (qAtom instanceof QuantBoundConstraint) {
					val = evaluateBoundConstraintKnownShared((QuantBoundConstraint) qAtom, subsMap);
				} else {
					val = evaluateLAEqualityKnownShared((QuantEquality) qAtom, subsMap);
				}
				if (arLit.isNegated()) {
					val = val.negate();
				}

				long time = System.nanoTime();
				if (val != mDefaultValueForLitDawgs) {
					final Dawg<SharedTerm, InstanceValue> remainderDawgForVarSub =
							Dawg.createConst(remainderDawgLengthForVar, val);
					transitionsFromVar.put(subs, remainderDawgForVarSub);
				}
				mQuantTheory.mDawgTime += System.nanoTime() - time;
			}
			long time = System.nanoTime();
			Dawg<SharedTerm, InstanceValue> dawgForVar = Dawg.createDawg(transitionsFromVar,
					Dawg.createConst(remainderDawgLengthForVar, mDefaultValueForLitDawgs));
			if (otherVar != null) {
				transitionsFromOtherVar.put(otherSubs,
						createAncestorDawg(dawgForVar, varPosInClause - firstVarPosInClause - 1));
			} else {
				remainderDawgAllVars = dawgForVar;
			}
			mQuantTheory.mDawgTime += System.nanoTime() - time;
		}
		long time = System.nanoTime();
		if (otherVar != null) {
			remainderDawgAllVars = Dawg.createDawg(transitionsFromOtherVar, Dawg.createConst(
					arLit.getClause().getVars().length - firstVarPosInClause - 1, mDefaultValueForLitDawgs));
		}
		final Dawg<SharedTerm, InstanceValue> litDawg =
				createAncestorDawg(remainderDawgAllVars, firstVarPosInClause);
		mQuantTheory.mDawgTime += System.nanoTime() - time;
		return litDawg;
	}

	/**
	 * Create an ancestor dawg for a given dawg and a given level. All transitions from the root until the given level
	 * are else-transitions, and the transition at the given level maps to the input dawg.
	 * 
	 * @param dawg
	 *            the remainder dawg.
	 * @param level
	 *            the number of levels the new dawg will be deeper than the given dawg.
	 * @return a new dawg with the given dawg as (only) sub-dawg at the given level.
	 */
	private Dawg<SharedTerm, InstanceValue> createAncestorDawg(final Dawg<SharedTerm, InstanceValue> dawg,
			final int level) {
		Dawg<SharedTerm, InstanceValue> prepended = dawg;
		for (int i = 0; i < level; i++) {
			prepended = Dawg.createDawg(Collections.emptyMap(), prepended);
		}
		return prepended;
	}

	/**
	 * Get all substitutions for this clause that result in a conflict or unit clause.
	 * 
	 * @param qClause
	 *            the quantified clause.
	 * @return the variable substitutions for the clause that lead to conflict or unit instances.
	 */
	private Collection<List<SharedTerm>> getConflictAndUnitSubsFromDawg(final QuantClause qClause,
			final Dawg<SharedTerm, InstanceValue> clauseDawg) {
		final Collection<List<SharedTerm>> conflictAndUnitSubs = new ArrayList<>();
		for (final Dawg.Entry<SharedTerm, InstanceValue> entry : clauseDawg.entrySet()) {
			assert !Config.EXPENSIVE_ASSERTS || isUsedValueForCheckpoint(entry.getValue());
			if (entry.getValue() != InstanceValue.IRRELEVANT) {
				// Replace the nulls (standing for the "else" case) with the suitable lambda
				boolean containsLambdas = false;
				final int nVars = qClause.getVars().length;
				final List<SharedTerm> subsWithNulls = entry.getKey();
				final List<SharedTerm> subs = new ArrayList<>(nVars);
				for (int i = 0; i < nVars; i++) {
					if (subsWithNulls.get(i) != null) {
						subs.add(subsWithNulls.get(i));
					} else {
						subs.add(mQuantTheory.getLambda(qClause.getVars()[i].getSort()));
						containsLambdas = true;
					}
				}
				assert containsLambdas || clauseDawg.getValue(subs) != InstanceValue.IRRELEVANT;
				// If the subs contains lambdas and the dawg contains transitions for them, check the value.
				// It might already be true, while the else case results in a different value.
				if (!containsLambdas || clauseDawg.getValue(subs) != InstanceValue.IRRELEVANT) {
					conflictAndUnitSubs.add(subs);
				}
			}
		}
		return conflictAndUnitSubs;
	}

	/**
	 * Helper method to build a map from Term to SharedTerm, given a map from Term to CCTerm.
	 */
	private Map<Term, SharedTerm> buildSharedMapFromCCMap(final Map<Term, CCTerm> ccMap) {
		final Map<Term, SharedTerm> sharedMap = new HashMap<>();
		for (Entry<Term, CCTerm> entry : ccMap.entrySet()) {
			final CCTerm ccTerm = entry.getValue();
			SharedTerm sharedTerm = ccTerm.getSharedTerm();
			sharedMap.put(entry.getKey(), sharedTerm);
		}
		return sharedMap;
	}

	/**
	 * Build a MutableAffineTerm from an SMTAffineTerm that may contain quantifiers, using a map that contains
	 * equivalent terms for the quantified summands.
	 * 
	 * @param smtAff
	 *            an SMTAffineTerm including quantified terms.
	 * @param sharedForQuantSmds
	 *            the equivalent shared terms for the quantified summands.
	 * @param source
	 *            the SourceAnnotation of the clause this SMTAffineTerm stems from.
	 * @return a MutableAffineTerm if each summand of the SMTAffineTerm either is ground or has an equivalent SharedTerm
	 *         storing a LinVar, null otherwise.
	 */
	private MutableAffineTerm buildMutableAffineTerm(final SMTAffineTerm smtAff,
			final Map<Term, SharedTerm> sharedForQuantSmds, SourceAnnotation source) {
		MutableAffineTerm at = new MutableAffineTerm();
		for (Entry<Term, Rational> entry : smtAff.getSummands().entrySet()) {
			final SharedTerm sharedTerm;
			if (entry.getKey().getFreeVars().length == 0) {
				sharedTerm = mClausifier.getSharedTerm(entry.getKey(), source);
			} else {
				sharedTerm = sharedForQuantSmds.get(entry.getKey());
				if (sharedTerm == null) {
					return null;
				}
			}
			Rational coeff = entry.getValue();
			if (sharedTerm.getOffset() != null) {
				LinVar var = sharedTerm.getLinVar();
				if (var != null) {
					at.add(coeff.mul(sharedTerm.getFactor()), var);
				}
				at.add(coeff.mul(sharedTerm.getOffset()));
			} else {
				return null;
			}
		}
		at.add(smtAff.getConstant());
		return at;
	}

	@SuppressWarnings("unchecked")
	/**
	 * Compute the substitutions for an arithmetical literal from a partial clause dawg, and from the bounds on the
	 * variables.
	 * 
	 * @param clause
	 *            the clause containing the arithmetical literals.
	 * @param arLits
	 *            the arithmetical literals in the clause.
	 * @param clauseDawg
	 *            the partial clause dawg containing information for all literals but the arithmetical ones.
	 * @return for each variable in the clause, the interesting substitutions.
	 */
	private SharedTerm[][] computeSubsForArithmetical(final QuantClause clause,
			final Collection<QuantLiteral> arLits, final Dawg<SharedTerm, InstanceValue> clauseDawg) {
		// TODO Rework this method

		// Collect all variables occurring in arithmetical literals, i.e., check which of them have any lower or upper
		// bounds
		final TermVariable[] clauseVars = clause.getVars();
		final int nClauseVars = clauseVars.length;
		final TermVariable[] clauseVarsInArLits = new TermVariable[nClauseVars];
		for (int i = 0; i < nClauseVars; i++) {
			final TermVariable var = clauseVars[i];
			if (!clause.getGroundBounds(var).isEmpty() || !clause.getVarBounds(var).isEmpty()) {
				clauseVarsInArLits[i] = var;
			}
		}

		// TODO Make sure that only representatives are added, similar to addAllInteresting
		final Set<SharedTerm>[] interestingTerms = new LinkedHashSet[nClauseVars];
		// All ground bounds are interesting terms
		for (int i = 0; i < nClauseVars; i++) {
			interestingTerms[i] = new LinkedHashSet<>();
			if (clauseVarsInArLits[i] != null) {
				interestingTerms[i].addAll(clause.getGroundBounds(clauseVarsInArLits[i]));
			}
		}
		// The substitutions for which the partial clause instance value is not yet true are interesting
		for (final Dawg.Entry<SharedTerm, InstanceValue> entry : clauseDawg.entrySet()) {
			if (entry.getValue() != InstanceValue.IRRELEVANT) {
				for (int i = 0; i < nClauseVars; i++) {
					if (clauseVarsInArLits[i] != null) {
						interestingTerms[i].add(entry.getKey().get(i));
					}
				}
			}
		}
		// Synchronize sets of variables which depend on another
		// TODO Use one method for this and synchronize... in clause
		boolean changed = true;
		while (changed) {
			changed = false;
			for (int i = 0; i < clauseVarsInArLits.length; i++) {
				final TermVariable var = clauseVarsInArLits[i];
				if (var != null) {
					for (TermVariable t : clause.getVarBounds(var)) {
						int j = clause.getVarIndex(t);
						changed = interestingTerms[i].addAll(interestingTerms[j]);
					}
				}
			}
		}

		final SharedTerm[][] interestingTermArrays = new SharedTerm[nClauseVars][];
		for (int i = 0; i < nClauseVars; i++) {
			interestingTermArrays[i] = interestingTerms[i].toArray(new SharedTerm[interestingTerms[i].size()]);
		}
		return interestingTermArrays;
	}

	/**
	 * Compute all interesting substitutions for a given clause.
	 * 
	 * This should only be called after updating the interesting terms for the clause.
	 * 
	 * @param quantClause
	 *            the quantified clause.
	 * @return a Set containing interesting substitutions for the clause.
	 */
	private Set<List<SharedTerm>> computeAllSubstitutions(QuantClause quantClause) {
		final int nVars = quantClause.getVars().length;
		Set<List<SharedTerm>> allSubs = new LinkedHashSet<>();
		allSubs.add(new ArrayList<SharedTerm>(nVars));
		for (int i = 0; i < nVars; i++) {
			Set<List<SharedTerm>> partialSubs = new LinkedHashSet<List<SharedTerm>>();
			for (final List<SharedTerm> oldSub : allSubs) {
				if (mClausifier.getEngine().isTerminationRequested()) {
					return Collections.emptySet();
				}
				assert !quantClause.getInterestingTerms()[i].isEmpty();
				for (final SharedTerm ground : quantClause.getInterestingTerms()[i].values()) {
					final List<SharedTerm> newSub = new ArrayList<>(nVars);
					newSub.addAll(oldSub);
					newSub.add(ground);
					partialSubs.add(newSub);
				}
			}
			allSubs.clear();
			allSubs.addAll(partialSubs);
		}
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
	 * @return the InstanceValue of the potential instance.
	 */
	private InstanceValue evaluateClauseInstance(final QuantClause quantClause, final List<SharedTerm> instantiation) {
		InstanceValue clauseValue = InstanceValue.FALSE;

		// Check ground literals first.
		for (Literal groundLit : quantClause.getGroundLits()) {
			if (groundLit.getAtom().getDecideStatus() == groundLit) {
				return combineForCheckpoint(clauseValue, InstanceValue.TRUE);
			} else if (groundLit.getAtom().getDecideStatus() == null) {
				clauseValue = combineForCheckpoint(clauseValue, InstanceValue.ONE_UNDEF);
			} else {
				assert groundLit.getAtom().getDecideStatus() != groundLit;
			}
		}
		// Only check clauses where all or all but one ground literals are set to false.
		if (clauseValue == InstanceValue.IRRELEVANT) {
			return clauseValue;
		}

		// Check quantified literals. TODO: Use SubstitutionHelper
		for (QuantLiteral quantLit : quantClause.getQuantLits()) {
			InstanceValue litValue = evaluateLitInstance(quantLit, instantiation);
			clauseValue = combineForCheckpoint(clauseValue, litValue);
			if (clauseValue == InstanceValue.IRRELEVANT) {
				return clauseValue;
			}
		}
		return clauseValue;
	}

	private Pair<InstanceValue, Boolean> evaluateNewClauseInstanceFinalCheck(final QuantClause quantClause,
			final List<SharedTerm> instantiation) {
		assert !mClauseInstances.containsKey(quantClause)
				|| !mClauseInstances.get(quantClause).containsKey(instantiation);
		InstanceValue clauseValue = InstanceValue.FALSE;

		// Check for true ground literals first.
		for (Literal groundLit : quantClause.getGroundLits()) {
			assert groundLit.getAtom().getDecideStatus() != null;
			if (groundLit.getAtom().getDecideStatus() == groundLit) {
				return new Pair<>(InstanceValue.TRUE, null);
			}
		}

		// Check quantified literals. TODO: Use SubstitutionHelper
		boolean hasOnlyKnownTerms = true;
		for (QuantLiteral quantLit : quantClause.getQuantLits()) {
			InstanceValue litValue = evaluateLitInstance(quantLit, instantiation); // TODO evaluateLitInstanceFinalCheck
			if (litValue == InstanceValue.UNKNOWN_TERM) {
				hasOnlyKnownTerms = false;
			}
			clauseValue = clauseValue.combine(litValue);
			if (clauseValue == InstanceValue.TRUE) {
				return new Pair<>(clauseValue, null);
			}
		}
		return new Pair<>(clauseValue, hasOnlyKnownTerms);
	}

	/**
	 * Instantiate a clause with a given substitution.
	 *
	 * @param clause
	 *            a clause containing at least one quantified literal.
	 * @param subs
	 *            the substitution terms for the variables in the clause.
	 *
	 * @return the set of ground literals, or null if the clause would be trivially true.
	 */
	private InstClause computeClauseInstance(final QuantClause clause, final List<SharedTerm> subs) {
		assert mClauseInstances.containsKey(clause);
		if (mClauseInstances.get(clause).containsKey(subs)) {
			return mClauseInstances.get(clause).get(subs);
		}

		final Map<TermVariable, Term> sigma = new LinkedHashMap<>();
		for (int i = 0; i < subs.size(); i++) {
			sigma.put(clause.getVars()[i], subs.get(i).getTerm());
		}
		final SubstitutionHelper instHelper = new SubstitutionHelper(mQuantTheory, clause.getGroundLits(),
				clause.getQuantLits(), clause.getSource(), sigma);
		instHelper.substituteInClause();
		Literal[] resultingLits = null;
		if (instHelper.getResultingClauseTerm() != mQuantTheory.getTheory().mTrue) {
			assert instHelper.getResultingQuantLits().length == 0;
			resultingLits = instHelper.getResultingGroundLits();
		}

		final InstClause inst =
				resultingLits != null ? new InstClause(clause, subs, Arrays.asList(resultingLits), -1) : null;
		mClauseInstances.get(clause).put(subs, inst);
		if (resultingLits != null) {
			mQuantTheory.getLogger().debug("Quant: instantiating quant clause %s results in %s", clause,
					Arrays.asList(resultingLits));
		}
		mQuantTheory.mNumInstancesProduced++;
		return inst;
	}

	/**
	 * Determine the value that an equality literal between two given CCTerm would have.
	 *
	 * @param left
	 *            The left side of the equality.
	 * @param right
	 *            The right side of the equality.
	 * @return Value True if the two terms are in the same congruence class, False if they are definitely distinct,
	 *         otherwise Undef if both CCTerms exists, Unknown else.
	 */
	private InstanceValue evaluateCCEqualityKnownShared(final QuantEquality qEq, final SubstitutionInfo info) {
		final CCTerm leftCC, rightCC;
		if (qEq.getLhs().getFreeVars().length == 0) {
			leftCC = mClausifier.getSharedTerm(qEq.getLhs(), qEq.mClause.getSource()).getCCTerm();
		} else {
			leftCC = info.getEquivalentCCTerms().get(qEq.getLhs());
		}
		if (qEq.getRhs().getFreeVars().length == 0) {
			rightCC = mClausifier.getSharedTerm(qEq.getRhs(), qEq.mClause.getSource()).getCCTerm();
		} else {
			rightCC = info.getEquivalentCCTerms().get(qEq.getRhs());
		}
		if (leftCC != null && rightCC != null) {
			if (mQuantTheory.getCClosure().isEqSet(leftCC, rightCC)) {
				return InstanceValue.TRUE;
			} else if (mQuantTheory.getCClosure().isDiseqSet(leftCC, rightCC)) {
				return InstanceValue.FALSE;
			} else {
				return InstanceValue.ONE_UNDEF;
			}
		}
		return mDefaultValueForLitDawgs;
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
	private InstanceValue evaluateCCEquality(final QuantEquality qEq, final List<SharedTerm> subs) {
		final QuantClause qClause = qEq.getClause();
		final SharedTermFinder finder = new SharedTermFinder(qClause.getSource(), qClause.getVars(), subs);
		final SharedTerm left = finder.findEquivalentShared(qEq.getLhs());
		final SharedTerm right = finder.findEquivalentShared(qEq.getRhs());
		if (left != null && right != null) {
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
		return mDefaultValueForLitDawgs;
	}

	/**
	 * Determine the value that an equality MutableAffineTerm = 0 would have if instantiated.
	 * 
	 * @param at
	 *            a MutableAffineTerm representing an LAEquality.
	 * @return Value True if both the lower and upper bound of at are 0, False if the lower bound is greater or the
	 *         upper bound is smaller than 0, Undef/Unknown else.
	 */
	private InstanceValue evaluateLAEqualityKnownShared(final QuantEquality qEq, final Map<Term, SharedTerm> sharedForQuant) {
		final SMTAffineTerm diff = new SMTAffineTerm(qEq.getLhs());
		diff.add(Rational.MONE, new SMTAffineTerm(qEq.getRhs()));

		final MutableAffineTerm at = buildMutableAffineTerm(diff, sharedForQuant, qEq.getClause().getSource());
		if (at != null) {
			final InfinitesimalNumber upperBound = mQuantTheory.mLinArSolve.getUpperBound(at);
			at.negate();
			final InfinitesimalNumber negLowerBound = mQuantTheory.mLinArSolve.getUpperBound(at);
			if (upperBound.signum() == 0 && negLowerBound.signum() == 0) {
				return InstanceValue.TRUE;
			} else if (upperBound.signum() < 0 || negLowerBound.signum() < 0) {
				return InstanceValue.FALSE;
			}
			return InstanceValue.ONE_UNDEF;
		}
		return mDefaultValueForLitDawgs;
	}

	/**
	 * Determine the value that an equality SMTAffineTerm = 0 would have if instantiated.
	 * 
	 * @param at
	 *            a MutableAffineTerm representing an LAEquality.
	 * @return Value True if both the lower and upper bound of at exist and are equal to 0, False if the lower bound
	 *         exists and is greater than 0, or the upper bound exists and is smaller than 0, Undef else.
	 */
	private InstanceValue evaluateLAEquality(final QuantEquality qEq, final List<SharedTerm> subs) {
		final SMTAffineTerm diff = new SMTAffineTerm(qEq.getLhs());
		diff.add(Rational.MONE, qEq.getRhs());

		final QuantClause qClause = qEq.getClause();
		final SharedTermFinder finder = new SharedTermFinder(qClause.getSource(), qClause.getVars(), subs);
		final SMTAffineTerm smtAff = finder.findEquivalentAffine(diff);
		if (smtAff != null) {
			final InfinitesimalNumber upperBound = mQuantTheory.mLinArSolve.getUpperBound(mClausifier, smtAff);
			smtAff.negate();
			final InfinitesimalNumber negLowerBound = mQuantTheory.mLinArSolve.getUpperBound(mClausifier, smtAff);
			if (upperBound.signum() == 0 && negLowerBound.signum() == 0) {
				return InstanceValue.TRUE;
			} else if (upperBound.signum() < 0 || negLowerBound.signum() < 0) {
				return InstanceValue.FALSE;
			}
			return InstanceValue.ONE_UNDEF;
		}
		return mDefaultValueForLitDawgs;
	}

	/**
	 * Determine the value that a bound constraint "term <= 0" would have.
	 *
	 * @param affine
	 *            The linear term for a constraint "term <= 0".
	 * @return Value True if the term has an upper bound <= 0, False if -term has a lower bound < 0, or Undef/Unknown
	 *         otherwise.
	 */
	private InstanceValue evaluateBoundConstraintKnownShared(final QuantBoundConstraint qBc,
			final Map<Term, SharedTerm> sharedForQuant) {
		final MutableAffineTerm at =
				buildMutableAffineTerm(qBc.getAffineTerm(), sharedForQuant, qBc.getClause().getSource());
		if (at == null) {
			return mDefaultValueForLitDawgs;
		}
		final InfinitesimalNumber upperBound = mQuantTheory.mLinArSolve.getUpperBound(at);
		if (upperBound.lesseq(InfinitesimalNumber.ZERO)) {
			return InstanceValue.TRUE;
		} else {
			at.negate();
			final InfinitesimalNumber lowerBound = mQuantTheory.mLinArSolve.getUpperBound(at);
			if (lowerBound.less(InfinitesimalNumber.ZERO)) {
				return InstanceValue.FALSE;
			} else {
				return InstanceValue.ONE_UNDEF;
			}
		}
	}

	/**
	 * Determine the value that a bound constraint "term <= 0" would have.
	 *
	 * @param affine
	 *            The linear term for a constraint "term <= 0".
	 * @return Value True if the term has an upper bound <= 0, False if -term has a lower bound < 0, or Undef otherwise.
	 */
	private InstanceValue evaluateBoundConstraint(final QuantBoundConstraint qBc, final List<SharedTerm> subs) {
		final SharedTermFinder finder =
				new SharedTermFinder(qBc.getClause().getSource(), qBc.getClause().getVars(), subs);
		final SMTAffineTerm affine = finder.findEquivalentAffine(qBc.getAffineTerm());
		if (affine == null) {
			return mDefaultValueForLitDawgs;
		}
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

	private class SharedTermFinder extends NonRecursive {
		private final SourceAnnotation mSource;
		private final List<TermVariable> mVars;
		private final List<SharedTerm> mInstantiation;
		private final Map<Term, SharedTerm> mSharedTerms;

		SharedTermFinder(final SourceAnnotation source, final TermVariable[] vars,
				final List<SharedTerm> instantiation) {
			mSource = source;
			mVars = Arrays.asList(vars);
			mInstantiation = instantiation;
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
					// Note: This will often not find a CC term.
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
	 * For pre-evaluation of QuantLiteral and QuantClause instances, we define the following values: TRUE if at least
	 * one literal evaluates to true, FALSE if all literals evaluate to false, ONE_UNDEF if all but one literal evaluate
	 * to false, and for this one all terms are known but not the value, UNKNOWN similarly but the terms are not known,
	 * OTHER for all other cases.
	 *
	 */
	private enum InstanceValue {
		TRUE, FALSE, ONE_UNDEF, UNKNOWN_TERM, OTHER, IRRELEVANT;

		private InstanceValue combine(InstanceValue other) {
			if (this == IRRELEVANT || other == IRRELEVANT) {
				return IRRELEVANT;
			} else if (this == TRUE || other == TRUE) {
				return TRUE;
			} else if (this == FALSE) {
				return other;
			} else if (other == FALSE) {
				return this;
			} else {
				return OTHER;
			}
		}

		private InstanceValue negate() {
			if (this == TRUE) {
				return FALSE;
			} else if (this == FALSE) {
				return TRUE;
			} else {
				return this;
			}
		}

		/**
		 * Restrict instance values to the given relevant values plus IRRELEVANT.
		 * 
		 * @param values
		 *            the relevant values.
		 * @return the InstanceValue itself, if contained in the relevant values, or IRRELEVANT else.
		 */
		private InstanceValue keepOnlyRelevant(final InstanceValue... values) {
			for (final InstanceValue val : values) {
				if (this == val) {
					return this;
				}
			}
			return IRRELEVANT;
		}
	}
}
