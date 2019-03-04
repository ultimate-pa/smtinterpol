/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprQuantifiedLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.UnitPropagationData;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

/**
 * Contains the procedures that manipulate the epr decide stack.
 *
 * @author Alexander Nutz
 */
public class DecideStackManager {


	private final LogProxy mLogger;
	private final EprTheory mEprTheory;
	private final EprStateManager mStateManager;

	private Set<EprClause> mUnitClausesWaitingForPropagation = new HashSet<>();

	private final EprDecideStack mDecideStack;

	public DecideStackManager(final LogProxy logger, final EprTheory eprTheory, final EprStateManager eprStateManager) {
		mLogger = logger;
		mEprTheory = eprTheory;
		mStateManager = eprStateManager;
		mDecideStack = new EprDecideStack(mLogger);
	}

	/**
	 * Takes a set of epr clauses, applies unit propagation until either a conflict is reached, or
	 * no more propagations are possible.
	 * Some clauses in the input set may have "normal" state, too, we just skip those.
	 * @param unitClauses a set of epr unit clauses
	 * @return null or a conflict epr clause
	 */
	EprClause propagateAll(final Set<EprClause> unitClauses) {
		final Set<EprClause> conflictsOrUnits = new HashSet<>(unitClauses);
		while (conflictsOrUnits != null
				&& !conflictsOrUnits.isEmpty()
				&& !mEprTheory.isTerminationRequested()) {
			final EprClause current = conflictsOrUnits.iterator().next(); // just pick any ..

			conflictsOrUnits.remove(current);

			if (!current.isUnit()) {
				// current clause has "normal" state --> ignore it
				assert !current.isConflict();
				continue;
			}

			final Set<EprClause> propResult = propagateUnitClause(conflictsOrUnits, current);

			if (propResult.isEmpty()) {
				continue;
			}

			if (propResult.iterator().next().isConflict()) {
				assert propResult.size() == 1;
				return propResult.iterator().next();
			}
			conflictsOrUnits.addAll(propResult);
		}
		return null;
	}

	/**
	 * Takes a set of unit clauses, together with one unit clause (not contained in the set)
	 * and makes a propagation according to the unit clause.
	 * If a conflict occurs, a singleton with just the conflict clause is returned.
	 * If additional clauses have been made unit, they are added to the set of unit clauses, and
	 * the updated set is returned.
	 * If no clause has been made conflict or unit by the propagation, the unit clause set is
	 * returned unchanged.
	 *
	 * @param conflictsOrUnits
	 * @param unitClause
	 * @return
	 */
	private Set<EprClause> propagateUnitClause(final Set<EprClause> conflictsOrUnits,
			final EprClause unitClause) {
		mLogger.debug("EPRDEBUG: EprStateManager.propagateUnitClause(..): " + unitClause);
		assert unitClause.isUnit();
		final Set<EprClause> result = new HashSet<>(conflictsOrUnits);

		// if we have a unit clause, propagate the literal
		// the set..-method returns the new set of conflicts or units

		/*
		 * one epr unit clause may yield many propagations
		 * --> iteratively set them, if one produces a conflict, go back to the outer epr dpll loop
		 *     if one produces more unit propagations, it is ok to just add them to conflictsOrUnits, because we
		 *      it contains unit clauses right now..
		 */
		final UnitPropagationData upd = unitClause.getUnitPropagationData();

		for (final DslBuilder dslB : upd.getQuantifiedPropagations()) {
			final Set<EprClause> newConflictsOrUnits = pushEprDecideStack(dslB);

			if (newConflictsOrUnits != null) {
				if (newConflictsOrUnits.iterator().next().isConflict()) {
					// in case of a conflict further propagations are obsolete
					return newConflictsOrUnits;
				} else if (newConflictsOrUnits.iterator().next().isUnit()) {
					result.addAll(newConflictsOrUnits);
					break; //TODO: surely break here?
				} else {
					assert false : "should not happen";
				}
			}
		}

		for (final Entry<Literal, Clause> en : upd.getGroundPropagations().entrySet()) {
			final Literal propLit = en.getKey();

			mEprTheory.addGroundLiteralToPropagate(propLit, en.getValue());
		}
		return result;
	}

	/**
	 * Compute (~choose) a ground conflict clause from the given set of EprConflict clauses
	 *  (which cannot be resolved by taking back an epr decision because there was none needed to
	 *   derive them)
	 *
	 * We may want to store other groundings somewhere perhaps ??..
	 *
	 * @param conflicts
	 * @return
	 */
	private Clause chooseGroundingFromConflict(final EprClause conflicts) {

		final Set<Clause> conflictGroundings = conflicts.getGroundings(conflicts.getConflictPoints());
		//TODO: pick smart?
		return conflictGroundings.iterator().next();
	}

	/**
	 * Resolve the given conflicts, i.e.,
	 *  - backtrack all unit propagations until the last decision
	 *  - explain the conflict accordingly, possibly learn some clauses
	 *
	 * @param conflicts
	 * @return A conflict that cannot be resolved in the EprTheory (given the current DPLL decide stack),
	 *    null if there exists none.
	 */
	Clause resolveConflict(final EprClause conflict) {
		mLogger.debug("EPRDEBUG: EprStateManager.resolveConflict(..): " + conflict);
		EprClause currentConflict = conflict;

		while (true) {
			currentConflict = currentConflict.factorIfPossible();
			assert currentConflict.isConflict();

			currentConflict = backjumpIfPossible(currentConflict);
			assert currentConflict == null || currentConflict.isConflict();

			if (currentConflict == null) {
				return null;
			}

			final DecideStackLiteral topMostDecideStackLiteral = mDecideStack.peekDecideStackLiteral();
			if (topMostDecideStackLiteral == null) {
				// we have come to the top of the decide stack --> return the conflict
				Clause groundConflict = chooseGroundingFromConflict(currentConflict);
				groundConflict = EprHelpers.sanitizeGroundConflict(mEprTheory.getClausifier(), mLogger, groundConflict);
				return groundConflict;
			}

			if (topMostDecideStackLiteral instanceof DecideStackDecisionLiteral) {
				/*
				 * Reaching here means that the clause
				 *  - contains two instances of the same predicate with the same polarity
				 *  which are
				 *  1 both refuted by the topmost decision
				 *  2 disjoint their allowed groundings
				 *
				 *  if 1 would not be the case the clause would not be a conflcit anymore
				 *  if 2 would not be the case we would have factored
				 *
				 *  --> we need to restrict our decision to set one of the two
				 */
				mDecideStack.popDecideStackLiteral();
				final Clause groundConflictOrNull = refine((DecideStackDecisionLiteral) topMostDecideStackLiteral, currentConflict);
				assert EprHelpers.verifyConflictClause(groundConflictOrNull, mLogger);
				return groundConflictOrNull;
			} else if (topMostDecideStackLiteral instanceof DecideStackPropagatedLiteral) {
				final EprClause newConflict = explainConflictOrSkip(
						currentConflict,
						(DecideStackPropagatedLiteral) topMostDecideStackLiteral);
				// now the conflict does not depend on the topMostDecideStackLiteral (anymore), thus we can pop the decide stack..
				mDecideStack.popDecideStackLiteral();
				assert newConflict.isConflict();
				currentConflict = newConflict;
			} else {
				assert false : "should not happen";
			}
		}
	}

	/**
	 * The top of the decision stack is a decision and we have a conflict clause.
	 * Refine that decision such that the conflict clause becomes a unit clause.
	 *
	 * @param topMostDecideStackLiteral
	 * @param currentConflict
	 * @return a ground conflict if the new decision immediately led to one
	 */
	private Clause refine(final DecideStackDecisionLiteral topMostDecideStackLiteral, final EprClause currentConflict) {

		// find all clause literals with the same predicate and polarity
		final Set<ClauseEprLiteral> literalsMatchingDecision = new HashSet<>();
		for (final ClauseLiteral cl : currentConflict.getLiterals()) {
			if (cl instanceof ClauseEprLiteral) {
				final ClauseEprLiteral cel = (ClauseEprLiteral) cl;
				if (cel.getPolarity() != topMostDecideStackLiteral.getPolarity()) {
					continue;
				}
				if (cel.getEprPredicate() != topMostDecideStackLiteral.getEprPredicate()) {
					continue;
				}
				literalsMatchingDecision.add(cel);
			}
		}
		// (invariant here: the dawgs of all cl literalsMatchingDecision - the refuted points,
		//  as all points are refuted on those dawgs - are all disjoint)

		// pick one literal (TODO: this is a place for a heuristic strategy)
		final ClauseEprLiteral pickedLit = literalsMatchingDecision.iterator().next();
		//.. and remove its dawg from the decision
		DawgState<ApplicationTerm, Boolean> newDawg = topMostDecideStackLiteral.getDawg();
		for (final IEprLiteral dsl : pickedLit.getPartiallyConflictingDecideStackLiterals()) {
			// assert EprHelpers.haveSameSignature(dsl.getDawg(), newDawg);
			newDawg = mEprTheory.getDawgFactory().createDifference(newDawg, dsl.getDawg());
		}

		// revert the decision
		final DecideStackLiteral dsdl = mDecideStack.popDecideStackLiteral();
		assert dsdl == topMostDecideStackLiteral;

		// make the new decision with the new dawg
		final DslBuilder dslb = new DslBuilder(dsdl.getPolarity(), dsdl.getEprPredicate(), newDawg, true);
		final Set<EprClause> newConflictsOrUnits = pushEprDecideStack(dslb);
		assert currentConflict.isUnit();
		return resolveConflictOrStoreUnits(newConflictsOrUnits);
	}

	/**
	 * Checks if the given conflict clause allows backjumping below an epr decision.
	 * If the argument clause does allow backjumping (i.e. is unit below the last epr decision), we
	 *  backtrack the decision an propagate according to the unit clause that the argument has become.
	 *  These propagations may result in another conflict, which we then return, or they may just at saturation,
	 *   then we return null.
	 * If the argument does not allow backjumping we return it unchanged.
	 * @param currentConflict a conflict clause
	 * @return a) the input conflict if backjumping is impossible,
	 *         b) another conflict if backjumping and propagation led to it,
	 *         c) null if backjumping was done and did not lead to a conflict through unit propagation
	 */
	private EprClause backjumpIfPossible(final EprClause currentConflict) {
		if (!mDecideStack.containsDecisions()) {
			return currentConflict;
		}

		final DecideStackDecisionLiteral lastDecision = mDecideStack.getLastDecision();

		if (false) {
			// we can backjump
			popEprDecideStackUntilAndIncluding(lastDecision);

			assert currentConflict.isUnit();
			// after the changes to the decide stack, is a unit clause --> just propagate accordingly
			mUnitClausesWaitingForPropagation.add(currentConflict);
			mLogger.debug("EPRDEBUG: (EprStateManager): backjumping, new unit clause/former conflict: "
					+ currentConflict + " reverted decision: " + lastDecision);
			return null;
		}
		return currentConflict;
	}

	/**
	 * Explains a conflict given a decide stack literal
	 *  - if the decide stack literal did not contribute to the conflict (does not contradict one
	 *   of the literals in the conflict), return the conflict unchanged (DPLL operation "skip")
	 *  - otherwise, if the decide stack literal contributed to the conflict, return the resolvent
	 *    of the conflict and the unit clause responsible for setting the decide stack literal
	 *     (DPLL operation "explain")
	 *
	 *   Note that this method does nothing to the decide stack.
	 * @param conflict the current conflict clause
	 * @param propagatedLiteral the current top of the decide stack.
	 * @return the resolvent from the conflict and the reason for the unit propagation of decideStackLiteral
	 */
	private EprClause explainConflictOrSkip(final EprClause conflict, final DecideStackPropagatedLiteral propagatedLiteral) {

		//look for the ClauseLiteral that propagatedLiteral conflicts with
		final Set<ClauseEprLiteral> relevantConfLits = new HashSet<>();
		for (final ClauseLiteral cl : conflict.getLiterals()) {
			if (!(cl instanceof ClauseEprLiteral)) {
				// cl's predicate is not an epr predicate, the decide stack only talks about epr predicates
				continue;
			}
			final ClauseEprLiteral cel = (ClauseEprLiteral) cl;
			if (!(cel.getPartiallyConflictingDecideStackLiterals().contains(propagatedLiteral))) {
				// propagatedLiteral does not conflict with the current ClauseLiteral (cl)
				continue;
			}

			if (cel instanceof ClauseEprQuantifiedLiteral) {
				final ClauseEprQuantifiedLiteral ceql = (ClauseEprQuantifiedLiteral) cel;
				DawgState<ApplicationTerm, Boolean> dawgChanged = propagatedLiteral.getDawg();
				dawgChanged = mEprTheory.getDawgFactory().projectWithMap(dawgChanged,
						ceql.getTranslationFromEprPredicateToClauseConstants());
				dawgChanged = mEprTheory.getDawgFactory().remap(dawgChanged,
						ceql.getTranslationFromEprPredicateToClauseVariables(), conflict.getVariables());
				dawgChanged = mEprTheory.getDawgFactory().createIntersection(dawgChanged, conflict.getConflictPoints());
				if (DawgFactory.isEmpty(dawgChanged)) {
					continue;
				}
				relevantConfLits.add(cel);
			} else {
				/*
				 * cel is a ground epr literal, and the propagatedLiteral is listed in partially conflicting literals with cel
				 * -- this means they conflict on all conflict points (because all variables are "don't care for cel).
				 */
				relevantConfLits.add(cel);
			}
		}

		if (relevantConfLits.size() >= 1) {
			// explain case, do resolution with the reason clause of the propagated literal

			/*
			 * An example for a legitimate case with more than one relevantConfLit is:
			 *  propagatedLiteral: EQ, (reflexive points)
			 *   (happens for example in orr-sanitized-eeaa/csll_is_h_on_cycle.imp.smt2, in the second push block)
			 *  conflict clause, with conflict grounding:  {..., EQ(i, i), EQ(j, j), ...}
			 *   --> the point (i, i), (j, j) may be instantiated from different quantified variables, the conflict point
			 *       leads to that instantiation
			 *   --> we cannot factor here
			 *   Solution: we just do a resolution/explain for each relevantConfLit
			 */
			EprClause resolvent = null;
			final ClauseEprLiteral confLit = relevantConfLits.iterator().next();
			resolvent = mEprTheory.getEprClauseFactory().createResolvent(confLit, propagatedLiteral.getReasonClauseLit());
			assert resolvent.isConflict();

			if (relevantConfLits.size() > 1) {
				resolvent = explainConflictOrSkip(resolvent, propagatedLiteral);
				assert resolvent.isConflict();
			}
			assert resolvent != null;
			return resolvent;
		} else {
			// skip case -- propagatedLiteral has nothing to do with conflictClause
			return conflict;
		}
	}

	/**
	 *
	 * @return 	A DecideStackLiteral for an EprPredicate with incomplete model
	 *           or null if all EprPredicates have a complete model.
	 **/
	DslBuilder getNextDecision() {
		for (final EprPredicate ep : mEprTheory.getStateManager().getAllEprPredicates()) {
			final DslBuilder decision = ep.getNextDecision();
			if (decision != null) {
				return decision;
			}
		}
		return null;
	}

	/**
	 *
	 * plan:
	 * - remove the conflicting point (option: more points?)
	 * - remove the top of the decide stack until the conflicting literal
	 * - if the conflictingDsl was a decision, resetting that decision is enough.. (just go back to DPLLEngine)
	 * - if the conflictingDsl was propagated, resolve its unit clause (it became a conflict through the setLiteral)
	 *
	 * @param egpl the epr ground literal that the DPLLEngine has set and which contradicts the current epr decide stack
	 * @param conflictingDsl the decide stack literal that egpl has the conflict with
	 * @return an unresolvable groundConflict if there is one, null if there is none
	 *         (i.e. changing an epr decision removed the inconsistency)
	 */
	Clause resolveDecideStackInconsistency(final EprGroundPredicateLiteral egpl, final DecideStackLiteral conflictingDsl) {

		// pop the decide stack above conflictingDsl
		final boolean success = popEprDecideStackUntilAndIncluding(conflictingDsl);
		assert success;


		if (conflictingDsl instanceof DecideStackDecisionLiteral) {
			// the old decision has been reverted, make a new one that is consistent
			// with the setting of egpl

			// TODO: this is a place for a strategy
			// right now: make decision as before, except for that one point
			final DawgState<ApplicationTerm, Boolean> newDawg =
					mEprTheory.getDawgFactory().createDifference(conflictingDsl.getDawg(), egpl.getDawg());

			final DslBuilder newDecision =
					new DslBuilder(
							conflictingDsl.getPolarity(), conflictingDsl.getEprPredicate(), newDawg, true);

			final Set<EprClause> conflictsOrUnits = pushEprDecideStack(newDecision);
			return resolveConflictOrStoreUnits(conflictsOrUnits);
		} else if (conflictingDsl instanceof DecideStackPropagatedLiteral) {
			/*
			 * the propagated literal that was the root of the inconsistency has been popped
			 * its reason for propagation should be a conflict now instead of a unit
			 * resolve that conflict
			 */
			final EprClause propReason = ((DecideStackPropagatedLiteral) conflictingDsl).getReasonClauseLit().getClause();
			propReason.updateStateWrtDecideStackLiteral(
					egpl,
					egpl.getEprPredicate().getAllEprClauseOccurences().get(propReason));
			assert propReason.isConflict();
			return resolveConflict(propReason);
		} else {
			assert false : "should not happen";
		}
		return null;
	}


	/**
	 * Pop the decide stack until -and including the argument- dsl is reached.
	 *
	 * @param dsl
	 * @return true if dsl was on the decide stack false otherwise
	 */
	private boolean popEprDecideStackUntilAndIncluding(final DecideStackLiteral dsl) {
		assert dsl != null;
		while (true) {
			final DecideStackLiteral currentDsl = mDecideStack.popDecideStackLiteral();
			if (currentDsl == dsl) {
				return true;
			} else if (currentDsl == null) {
				assert false :
					"could not find the conflicting decide stack literal that was found earlier";
				return false;
			}
		}
	}

	/**
	 * Given an epr ground literal look if there is a decide stack literal that contradicts it.
	 * (this is called when the DPLLEngine sets an epr literal an we need to know if the two decide stacks
	 *  of dpll engine and epr theory are still consistent wrt each other)
	 * Note that the result should be unique here, because on the epr decide stack we don't set points twice
	 * @param egpl
	 * @return the decide stack literal that contradicts egpl if there exists one, null otherwise
	 */
	DecideStackLiteral searchConflictingDecideStackLiteral(final EprGroundPredicateLiteral egpl) {
		// TODO not fully sure if each point is set at most only once on the epr decide stack
		//  --> if not, we probably want to
		for (final IEprLiteral dsl : egpl.getEprPredicate().getEprLiterals()) {
			if (!(dsl instanceof DecideStackLiteral)) {
				continue;
			}
			if (dsl.getPolarity() != egpl.getPolarity()
					&& !DawgFactory
							.isEmpty(mEprTheory.getDawgFactory().createIntersection(egpl.getDawg(), dsl.getDawg()))) {
				return (DecideStackLiteral) dsl;
			}
		}
		return null;
	}

	public Clause resolveConflictOrStoreUnits(final Set<EprClause> conflictOrUnits) {
		if (conflictOrUnits == null || conflictOrUnits.isEmpty()) {
			return null;
		}
		if (conflictOrUnits.iterator().next().isConflict()) {
			return resolveConflict(conflictOrUnits.iterator().next());
		}
		if (conflictOrUnits.iterator().next().isUnit()) {
			mUnitClausesWaitingForPropagation.addAll(conflictOrUnits);
		}
		return null;
	}

	/**
	 * Apply the consequences of setting the given epr decide stack literal
	 *  - wrt. the decide stack of the DPLLEngine
	 *  - wrt. the epr clauses
	 *  both can yield conflicts or unit propagations.
	 *
	 * @param dsl
	 * @return
	 */
	Set<EprClause> pushEprDecideStack(final DslBuilder dslb) {
		dslb.setDecideStackIndex(mDecideStack.height() + 1);
		final DecideStackLiteral dsl = dslb.build();

		/*
		 * We need to do the interal push operation first, because otherwise the
		 * coming operations (setting covered atoms, updating the clause states)
		 * encounter an inconsistent state (i.e. a decide stack literal being registered in
		 * an epr predicate but not present on the decide stack).
		 */
		mDecideStack.pushDecideStackLiteral(dsl);

		/*
		 * setting the decideStackLiteral means that we have to set all ground atoms covered by it
		 * in the DPLLEngine
		 * however, if we propagate a ground literal here, we also have to give a ground unit clause for it
		 * creating this ground unit clause may lead to new ground atoms, thus we make a copy to a void
		 * concurrent modification of the list of DPLLAtoms, and repeat until the copy does not change
		 * TODO: can we do this nicer?
		 */
		boolean newDPLLAtoms = true;
		while (newDPLLAtoms) {
			final HashSet<EprGroundPredicateAtom> copy = new HashSet<>(dsl.getEprPredicate().getDPLLAtoms());
			for (final EprGroundPredicateAtom atom : copy) {
				final EprClause conflict = mStateManager.setGroundAtomIfCoveredByDecideStackLiteral(dsl, atom);
				if (conflict != null) {
					return new HashSet<>(Collections.singleton(conflict));
				}
			}
			newDPLLAtoms = !copy.equals(dsl.getEprPredicate().getDPLLAtoms());
		}


		// inform the clauses...
		// check if there is a conflict
		final Set<EprClause> conflictsOrPropagations =
				mStateManager.getEprClauseManager().updateClausesOnSetEprLiteral(dsl);


		return conflictsOrPropagations;
	}

	/**
	 * Returns true iff the EprTheory has currently made no own decisions.
	 * Thus when we derived something in the epr theory, we can propagate it, otherwise
	 * we can only suggest it..
	 * @return
	 */
	boolean isDecisionLevel0() {
		return !mDecideStack.containsDecisions();
	}

	void pushOnSetLiteral(final Literal l) {
		mDecideStack.pushSetLiteral(l);
	}

	/**
	 * Pops the epr decide stack until the set literal marker belonging to the given literal.
	 *
	 * @param l
	 */
	void popOnBacktrackLiteral(final Literal l) {
		mDecideStack.popBacktrackLiteral(l);
	}


	/**
	 * When the dpll engine pops an epr ground predicate literal, we may have to pop further than to its marker. We also
	 * need to pop until the epr decide stack literal that covers the literal and thus was the reason for its
	 * propagation. If we did not do this, we would end up with inconsistent dpll/epr decide stack state.
	 */
	void popReasonsOnBacktrackEprGroundLiteral(final EprGroundPredicateLiteral egpl) {

		assert DawgFactory.isSingleton(egpl.getDawg());
		for (final IEprLiteral el : egpl.getEprPredicate().getEprLiterals()) {
			if (el instanceof EprGroundPredicateLiteral) {
				assert el != egpl : "we just backtracked the literal " + egpl + " it should have been unregistered";
				// we have a different ground predicate literal -- two epr ground predicate literals, that are on the
				// decide stack
				// don't talk to each other (otherwise the decide stack has redundancy or is inconsistent)
				assert DawgFactory.isEmpty(mEprTheory.getDawgFactory().createIntersection(el.getDawg(),
						egpl.getDawg())) : "redundancy or inconsistency in decide stack before backtrack";
				continue;
			}
			// el is a DecideStackLiteral
			final DecideStackLiteral dsl = (DecideStackLiteral) el;


			final List<ApplicationTerm> point = DawgFactory.getSet(egpl.getDawg()).iterator().next();
			if (!dsl.getDawg().getValue(point)) {
				// el does not talk about the point egpl is concerned with
				continue;
			}
			// el talks about egpl's point --> we need to pop the decide stack until el

			assert el.getPolarity() == egpl.getPolarity() : "epr decide stack was inconsistent before backtrack.";

			mLogger.debug("EPRDEBUG: DecideStackManager.popReasonsOnBacktrack..(..): "
					+ "needed to pop further than setLiteralMarker, until reason DecideStackLiteral: " + dsl);
			this.popEprDecideStackUntilAndIncluding(dsl);
			// there can be only one reason (unless the epr decide stack is has redundancies in the DecideStackLiterals)
			// so we can return at this point
			return;
		}
	}

	Clause doPropagations() {
		final HashSet<EprClause> toProp = new HashSet<>(mUnitClausesWaitingForPropagation);
		mUnitClausesWaitingForPropagation = new HashSet<>();
		final EprClause conflict = propagateAll(toProp);
		if (conflict == null) {
			return null;
		} else {
			assert conflict.isConflict();
			final Clause groundConflict =  resolveConflict(conflict);
			return groundConflict;
		}
	}

	public void push() {
		mDecideStack.push();
	}

	public void pop() {
		mUnitClausesWaitingForPropagation.clear();
		mDecideStack.pop();
	}

	public void removeFromUnitClauseSet(final EprClause eprClause) {
		mUnitClausesWaitingForPropagation.remove(eprClause);
	}

	/**
	 * When mEprliterals are accessed from the outside, verify if they satisfy some consistency criteria..
	 * @return
	 */
	public boolean verifyEprLiterals(final Set<IEprLiteral> eprLiterals) {
		// checks: is every decide stack literal actually present on the decide stack?
		for (final IEprLiteral el : eprLiterals) {
			if (el instanceof DecideStackLiteral
					&& !mDecideStack.mStack.contains(el)) {
				mLogger.debug("EPRDEBUG: DecideStackManager.verifyEprLiterals: the decide stack literal " + el +
						" is listed by its EprPredicate, but is not present on the decide stack.");
				return false;
			}
		}
		return true;
	}

	@Override
	public String toString() {
		return "DSM: " + mDecideStack;
	}

	private static class EprDecideStack {
		private final List<DecideStackEntry> mStack = new LinkedList<>();

		private int lastNonMarkerIndex = -1;
		private int lastPushMarkerIndex = -1;

		private DecideStackLiteral lastNonMarker;
		private DecideStackPushMarker lastPushMarker;
		private DecideStackEntry lastElement;
		private DecideStackDecisionLiteral lastDecision;

		private final Map<Literal, DecideStackSetLiteralMarker> mLiteralToMarker =
				new HashMap<>();

		private final LogProxy mLogger;

		public EprDecideStack(final LogProxy logger) {
			mLogger = logger;
		}

		/**
		 * Places a marker for a setLiteral operation. (When the DPLLEngine sets a literal..)
		 */
		void pushSetLiteral(final Literal l) {
			mLogger.debug("EPRDEBUG: EprDecideStack.pushSetLiteral(" + l + ")");
			final DecideStackSetLiteralMarker marker = new DecideStackSetLiteralMarker(l, height() + 1);
			lastElement = marker;
			mStack.add(marker);
			marker.push();
			assert !mLiteralToMarker.containsKey(l);
			mLiteralToMarker.put(l, marker);
			assert checkDecideStackInvariants();
		}

		public DecideStackDecisionLiteral getLastDecision() {
			assert lastDecision != null;
			return lastDecision;
		}

		/**
		 * @return true iff the decide stack contains one or more DecideStackDecisionLiterals
		 */
		public boolean containsDecisions() {
			return lastDecision != null;
		}

		void popBacktrackLiteral(final Literal l) {
			mLogger.debug("EPRDEBUG: EprDecideStack.popBacktrackLiteral(" + l + ")");
			final DecideStackSetLiteralMarker marker = mLiteralToMarker.remove(l);
			if (marker.nr >= height()) {
				// removed the marker through a pop() before, nothing to do
				return;
			}

			/*
			 * We clear the complete list above the given literal's marker, BUT, we restore all the pushMarkers
			 * in that list on the decideStack.
			 */
			final List<DecideStackPushMarker> pushMarkers = new ArrayList<>();

			final List<DecideStackEntry> suffix = mStack.subList(mStack.indexOf(marker), mStack.size());
			for (final DecideStackEntry dse : suffix) {
				dse.pop();
				if (dse instanceof DecideStackLiteral) {
					((DecideStackLiteral) dse).unregister();
				} else if (dse instanceof DecideStackPushMarker) {
					pushMarkers.add((DecideStackPushMarker) dse);
				}
			}
			suffix.clear();

			// restore the pushMarkers
			Collections.reverse(pushMarkers);
			mStack.addAll(pushMarkers);

			updateInternalFields();
			assert checkDecideStackInvariants();
		}

		DecideStackLiteral peekDecideStackLiteral() {
			return lastNonMarker;
		}

		/**
		 * Remove a DecideStackLiteral from the stack.
		 * Note that there may be markers above it on the stack that we have to leave -- i.e. our stack is not really a stack..
		 *
		 * @return
		 */
		DecideStackLiteral popDecideStackLiteral() {
			mLogger.debug("EPRDEBUG: EprDecideStack.popDecideStackLiteral()");
			if (lastNonMarker == null) {
				return null;
			}

			final DecideStackLiteral result = lastNonMarker;
			mStack.remove(result);
			result.pop();
			result.unregister();

			updateInternalFields();

			assert checkDecideStackInvariants();
			return result;
		}

		void pushDecideStackLiteral(final DecideStackLiteral dsl) {
			mLogger.debug("EPRDEBUG: EprDecideStack.pushDecideStackLiteral()");
			mStack.add(dsl);
			dsl.push();
			lastNonMarker = dsl;
			lastNonMarkerIndex = mStack.size() - 1;
			lastElement = dsl;
			if (dsl instanceof DecideStackDecisionLiteral) {
				lastDecision = (DecideStackDecisionLiteral) dsl;
			}
			assert checkDecideStackInvariants();
		}

		/**
		 * Returns the decide stack entries above the last push marker.
		 */
		List<DecideStackEntry> peek() {
			final List<DecideStackEntry> suffix = mStack.subList(lastPushMarkerIndex + 1, mStack.size());
			return suffix;
		}

		void pop() {
			assert lastPushMarker != null : "already popped all push markers";
			mLogger.debug("EPRDEBUG: EprDecideStack.pop()");

			// if (lastPushMarker == null) {
			// /*
			// * already popped below the last and only pushMarker
			// * (e.g. because a setLiteralMarker was popped)
			// * --> do nothing
			// */
			// }

			final List<DecideStackEntry> suffix = mStack.subList(lastPushMarkerIndex, mStack.size());
			for (final DecideStackEntry dse : suffix) {
				dse.pop();
				if (dse instanceof DecideStackLiteral) {
					((DecideStackLiteral) dse).unregister();
				}
			}
			suffix.clear();


			updateInternalFields();
			assert checkDecideStackInvariants();
		}

		void push() {
			mLogger.debug("EPRDEBUG: EprDecideStack.push()");

			final DecideStackPushMarker pm = new DecideStackPushMarker(height() + 1);
			lastPushMarker = pm;
			lastPushMarkerIndex = mStack.size();
			lastElement = pm;
			mStack.add(pm);
			assert checkDecideStackInvariants();
		}

		/**
		 * update the fields that track some relevant stack positions after one of the pop operations.
		 */
		private void updateInternalFields() {
			// change the fields accordingly -- search for the next non push marker
			final ListIterator<DecideStackEntry> it = mStack.listIterator(mStack.size());

			lastElement = mStack.isEmpty() ? null : mStack.get(mStack.size() - 1);

			boolean foundNonPushMarker = false;
			boolean foundPushMarker = false;
			boolean foundLastDecision = lastDecision == null || lastDecision.nr < height();

			while (it.hasPrevious()) {
				final DecideStackEntry prev = it.previous();

				if (!foundPushMarker && prev instanceof DecideStackPushMarker) {
					lastPushMarker = (DecideStackPushMarker) prev;
					lastPushMarkerIndex = it.previousIndex() + 1;
					foundPushMarker = true;
				}

				if (!foundNonPushMarker && prev instanceof DecideStackLiteral) {
					lastNonMarker = (DecideStackLiteral) prev;
					lastNonMarkerIndex = it.previousIndex() + 1;
					foundNonPushMarker = true;
				}

				if (!foundLastDecision && prev instanceof DecideStackDecisionLiteral) {
					lastDecision = (DecideStackDecisionLiteral) prev;
					foundLastDecision = true;
				}

				if (foundPushMarker && foundNonPushMarker && foundLastDecision) {
					break;
				}
			}
			if (!foundPushMarker) {
				lastPushMarker = null;
				lastPushMarkerIndex = -1;
			}
			if (!foundNonPushMarker) {
				lastNonMarker = null;
				lastNonMarkerIndex = -1;
			}
			if (!foundLastDecision) {
				lastDecision = null;
			}
			assert checkDecideStackInvariants();
		}

		/**
		 * Returns the index of the topmost entry on the decide stack (this is not identical with
		 * the number of elements on the stack, because we sometimes pop in the middle!).
		 * @return
		 */
		public int height() {
			return lastElement == null ? 0 : lastElement.nr;
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			for (final DecideStackEntry dse : mStack) {
				sb.append(dse.toString());
				sb.append("\n");
			}
			return sb.toString();
		}

		/**
		 * Method used for asserts.
		 */
		private boolean checkDecideStackInvariants() {
			boolean result = true;

			result &= height() >= mStack.size();
			assert result;

			final Iterator<DecideStackEntry> it = mStack.iterator();
			DecideStackEntry currentEntry = null;
			for (int i = 0; i < mStack.size(); i++) {
				final DecideStackEntry lastEntry = currentEntry;
				currentEntry = it.next();

				result &= lastEntry == null || lastEntry.nr < currentEntry.nr;
				assert result;

				result &= currentEntry.nr >= i;
				assert result;
			}

			return result;
		}
	}
}
