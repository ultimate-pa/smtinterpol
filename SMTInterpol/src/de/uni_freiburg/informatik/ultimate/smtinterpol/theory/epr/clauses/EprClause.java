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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.BinaryRelation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackDecisionLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.IEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;

/**
 * Represents a clause that is only known to the EprTheory.
 * This means that the clause typically contains at least one free
 * (implicitly forall-quantified) variable -- exceptions, i.e. ground EprClauses may occur through
 * factoring or resolution.
 *
 * @author Alexander Nutz
 */
public class EprClause {


	/**
	 * The literals in this clause, expressed as Literals (the type that the DPLLEngine knows..).
	 */
	private final Set<Literal> mDpllLiterals;

	private final EprTheory mEprTheory;
	private final DawgFactory<ApplicationTerm, TermVariable> mDawgFactory;

	private final Set<ClauseLiteral> mLiterals;

	/**
	 * Since the introduction of equality reflexivity clauses, we want to support EprClauses that are in fact ground.
	 */
	private final boolean mIsGround;

	/**
	 * Stores the variables occurring in this clause in the order determined by the HashMap mVariableToClauseLitToPositions
	 */
	private final SortedSet<TermVariable> mVariables;

	/**
	 * If this flag is true, the value of mEprClauseState can be relied on.
	 * Otherwise the state must be recomputed.
	 */
	boolean mClauseStateIsDirty = true;

	/**
	 * The current fulfillment state of this epr clause
	 */
	private EprClauseState mEprClauseState;

	private IDawg<ApplicationTerm, TermVariable> mConflictPoints;

	private UnitPropagationData mUnitPropagationData;

	/*
	 * stuff relative to the decide stack border; done as maps now, but maybe one item each is enough??
	 */
	private final Map<DecideStackLiteral, Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>>> mDecideStackBorderToClauseLitToUnitPoints =
			new HashMap<>();
	private final Map<DecideStackLiteral, EprClauseState> mDecideStackBorderToClauseState =
			new HashMap<>();
	private final Map<DecideStackLiteral, IDawg<ApplicationTerm, TermVariable>> mDecideStackBorderToConflictPoints =
			new HashMap<>();
	private final Map<DecideStackLiteral, UnitPropagationData> mDecideStackBorderToUnitPropagationData =
			new HashMap<>();

	private boolean mHasBeenDisposed = false;

	public EprClause(final Set<Literal> lits, final EprTheory eprTheory) {
		mDpllLiterals = lits;
		mEprTheory = eprTheory;
		mDawgFactory = eprTheory.getDawgFactory();

		// set up the clause..

		final Pair<SortedSet<TermVariable>, Set<ClauseLiteral>> resPair =
				 createClauseLiterals(lits);

		mLiterals = Collections.unmodifiableSet(resPair.getSecond());

		mVariables = Collections.unmodifiableSortedSet(resPair.getFirst());

		mIsGround = mVariables.isEmpty();

		registerFulfillingOrConflictingEprLiteralInClauseLiterals();
	}


	private void registerFulfillingOrConflictingEprLiteralInClauseLiterals() {
		for (final ClauseLiteral cl : getLiterals()) {
			if (!(cl instanceof ClauseEprLiteral)) {
				continue;
			}
			final ClauseEprLiteral cel = (ClauseEprLiteral) cl;
			for (final IEprLiteral dsl : cel.getEprPredicate().getEprLiterals()) {
				if (cel.isDisjointFrom(dsl.getDawg())) {
					continue;
				}

				if (dsl.getPolarity() == cel.getPolarity()) {
					cel.addPartiallyFulfillingEprLiteral(dsl);
				} else {
					cel.addPartiallyConflictingEprLiteral(dsl);
				}
			}
		}
	}


	/**
	 * Set up the clause in terms of our Epr data structures.
	 * Fills the fields mVariableToClauseLitPositionsTemp and mLiteralsTemp.
	 *
	 * TODOs:
	 *  - detect tautologies
	 *  - detect duplicate literals
	 *
	 * @param lits The (DPLL) literals that this clause is created from.
	 * @return
	 * @return
	 */
	private Pair<SortedSet<TermVariable>, Set<ClauseLiteral>> createClauseLiterals(final Set<Literal> lits) {

		final SortedSet<TermVariable> variables = new TreeSet<>(EprHelpers.getColumnNamesComparator());
		final HashSet<ClauseLiteral> literals = new HashSet<>();

//		Set<EprQuantifiedEqualityAtom> quantifiedEqualities = new HashSet<EprQuantifiedEqualityAtom>();

		for (final Literal l : lits) {
			final boolean polarity = l.getSign() == 1;
			final DPLLAtom atom = l.getAtom();

			if (atom instanceof EprQuantifiedPredicateAtom
					|| atom instanceof EprQuantifiedEqualityAtom) {
				final EprQuantifiedPredicateAtom eqpa = (EprQuantifiedPredicateAtom) atom;

				variables.addAll(
						Arrays.asList(
								atom.getSMTFormula(mEprTheory.getTheory()).getFreeVars()));

				final ClauseEprQuantifiedLiteral newL = new ClauseEprQuantifiedLiteral(
						polarity, eqpa, this, mEprTheory);
				literals.add(newL);
				eqpa.getEprPredicate().addQuantifiedOccurence(newL, this);

				continue;
			} else if (atom instanceof EprGroundPredicateAtom) {
				final EprGroundPredicateAtom egpa = (EprGroundPredicateAtom) atom;
				final ClauseEprGroundLiteral newL = new ClauseEprGroundLiteral(
						polarity, egpa, this, mEprTheory);
				literals.add(newL);
				egpa.getEprPredicate().addGroundOccurence(newL, this);
				continue;
//			} else if (atom instanceof EprQuantifiedEqualityAtom) {
//
//				todo

//				// quantified equalities we don't add to the clause literals but
//				// just collect them for adding exceptions to the other quantified
//				// clause literals later
//				assert atom == l : "should have been eliminated by destructive equality reasoning";
//				quantifiedEqualities.add((EprQuantifiedEqualityAtom) atom);
//				continue;
			} else if (atom instanceof EprGroundEqualityAtom) {
				assert false : "do we really have this case?";
				continue;
//			} else if (atom instanceof CCEquality) {
//				(distinction form DPLLAtom does not seem necessary)
//				continue;
			} else {
				// atom is a "normal" Atom from the DPLLEngine
				literals.add(
						new ClauseDpllLiteral(polarity, atom, this, mEprTheory));
				continue;
			}
		}

//		for (ClauseLiteral cl : literals) {
//			if (cl instanceof ClauseEprQuantifiedLiteral) {
//				ClauseEprQuantifiedLiteral ceql = (ClauseEprQuantifiedLiteral) cl;
//				// update all quantified predicate atoms according to the quantified equalities
//				// by excluding the corresponding points in their dawgs
//				ceql.addExceptions(quantifiedEqualities);
//			}
//		}

//		assert literals.size() == mDpllLiterals.size() - quantifiedEqualities.size();

		return new Pair<>(
				variables, literals);

	}

	/**
	 * Removes the traces of the clause in the data structures that link to it.
	 * The application I can think of now is a pop command.
	 */
	public void disposeOfClause() {
		assert !mHasBeenDisposed;
		for (final ClauseLiteral cl : mLiterals) {
			if (cl instanceof ClauseEprLiteral) {
				final ClauseEprLiteral cel = (ClauseEprLiteral) cl;
				cel.getEprPredicate().notifyAboutClauseDisposal(this);
			}
		}
		mEprTheory.getStateManager().getDecideStackManager().removeFromUnitClauseSet(this);
		mHasBeenDisposed = true;
	}

	/**
	 * Update the necessary data structure that help the clause to determine which state it is in.
	 *  --> determineState does not work correctly if this has not been called before.
	 * @param dsl
	 * @param literalsWithSamePredicate
	 * @return
	 */
	public void updateStateWrtDecideStackLiteral(final IEprLiteral dsl,
			final Set<ClauseEprLiteral> literalsWithSamePredicate) {
		assert !mHasBeenDisposed;

		mClauseStateIsDirty = true;

		// update the storage of each clause literal that contains the decide stack literals
		// the clause literal is affected by
		for (final ClauseEprLiteral cel : literalsWithSamePredicate) {
			assert cel.getClause() == this;

			if (cel.isDisjointFrom(dsl.getDawg())) {
				continue;
			}

			if (cel.getPolarity() == dsl.getPolarity()) {
				cel.addPartiallyFulfillingEprLiteral(dsl);
			} else {
				cel.addPartiallyConflictingEprLiteral(dsl);
			}
		}
	}


	public void backtrackStateWrtDecideStackLiteral(final DecideStackLiteral dsl) {
		mClauseStateIsDirty = true;
	}

	/**
	 * This clause is informed that the DPLLEngine has set literal.
	 * The fulfillmentState of this clause may have to be updated because of this.
	 *
	 * @param literal ground Epr Literal that has been set by DPLLEngine
	 * @return
	 */
	public EprClauseState updateStateWrtDpllLiteral(final Literal literal) {
		assert !mHasBeenDisposed;
		mClauseStateIsDirty = true;
		return determineClauseState(null);
	}

	public void backtrackStateWrtDpllLiteral(final Literal literal) {
		assert !mHasBeenDisposed;
		mClauseStateIsDirty = true;
	}

	/**
	 * Checks if, in the current decide state, this EprClause is
	 *  a) a conflict clause or
	 *  b) a unit clause
	 * .. on at least one grounding.
	 *
	 * TODO: this is a rather naive implementation
	 *   --> can we do something similar to two-watchers??
	 *   --> other plan: having a multi-valued dawg that count how many literals are fulfillable
	 *       for each point
	 *
	 * @return a) something that characterized the conflict (TODO: what excactly?) or
	 *         b) a unit literal for propagation (may be ground or not)
	 *         null if it is neither
	 */
	private EprClauseState determineClauseState(final DecideStackLiteral decideStackBorder) {

		// do we have a literal that is fulfilled (on all points)?
		for (final ClauseLiteral cl : getLiterals()) {
//			if (mEprTheory.isTerminationRequested()) {
////				throw new AssertionError("terminated");
//				break;
//			}

			if (cl.isFulfilled(decideStackBorder)) {
				setClauseState(decideStackBorder, EprClauseState.Fulfilled);
				return getClauseState(decideStackBorder);
			}
		}

		// Although the whole literal is not fulfilled, some points may be..
		// we only need to consider points where no literal is decided "true" yet..
		IDawg<ApplicationTerm, TermVariable> pointsToConsider =
				mEprTheory.getDawgFactory().getUniversalDawg(getVariables());
		for (final ClauseLiteral cl : getLiterals()) {
//			if (mEprTheory.isTerminationRequested()) {
////				throw new AssertionError("terminated");
//				break;
//			}

			if (cl.isRefuted(decideStackBorder)) {
				continue;
			}

			if (cl instanceof ClauseEprQuantifiedLiteral) {
				final IDawg<ApplicationTerm, TermVariable> clFulfilledPoints =
						((ClauseEprQuantifiedLiteral) cl).getFulfilledPoints();
//				pointsToConsider.removeAll(clFulfilledPoints);
				pointsToConsider = pointsToConsider.difference(clFulfilledPoints);
			}
		}
		assert EprHelpers.verifySortsOfPoints(pointsToConsider, getVariables());


		/**
		 * The set of all points (over this clause's signature, read: groundings) where no literal of this
		 * clause is fulfillable
		 *  --> once the computation is complete, this represents the set of groundings that are a conflict.
		 */
		IDawg<ApplicationTerm, TermVariable> pointsWhereNoLiteralsAreFulfillable =
				mDawgFactory.copyDawg(pointsToConsider);
		IDawg<ApplicationTerm, TermVariable> pointsWhereOneLiteralIsFulfillable =
				mDawgFactory.getEmptyDawg(getVariables());
		IDawg<ApplicationTerm, TermVariable> pointsWhereTwoOrMoreLiteralsAreFulfillable =
				mDawgFactory.getEmptyDawg(getVariables());
		assert EprHelpers.haveSameSignature(pointsWhereNoLiteralsAreFulfillable,
				pointsWhereOneLiteralIsFulfillable,
				pointsWhereTwoOrMoreLiteralsAreFulfillable);

		Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> clauseLitToPotentialUnitPoints =
				new HashMap<>();


		for (final ClauseLiteral cl : getLiterals()) {
//			if (mEprTheory.isTerminationRequested()) {
//				break;
//			}

			if (cl.isFulfillable(decideStackBorder)) {
				// at least one point of cl is still undecided (we sorted out fulfilled points before..)
				// we move the newly fulfillable points one up in our hierarchy

				IDawg<ApplicationTerm, TermVariable> toMoveFromNoToOne;
				IDawg<ApplicationTerm, TermVariable> toMoveFromOneToTwo;
				if (cl instanceof ClauseEprQuantifiedLiteral) {
					final IDawg<ApplicationTerm, TermVariable> fp =
							((ClauseEprQuantifiedLiteral) cl).getFulfillablePoints(decideStackBorder);

					toMoveFromNoToOne = pointsWhereNoLiteralsAreFulfillable.intersect(fp);
					toMoveFromOneToTwo = pointsWhereOneLiteralIsFulfillable.intersect(fp);
				} else {
					/*
					 *  if cl is ground, the dawg of the current cl is the full dawg
					 *   --> intersecting something with the full dawg means copying the something..
					 */
					toMoveFromNoToOne = mDawgFactory.copyDawg(pointsWhereNoLiteralsAreFulfillable);
					toMoveFromOneToTwo = mDawgFactory.copyDawg(pointsWhereOneLiteralIsFulfillable);
				}

				assert EprHelpers.haveSameSignature(toMoveFromNoToOne, toMoveFromOneToTwo, pointsWhereNoLiteralsAreFulfillable);

				/*
				 * move all the fulfillable point of the current ClauseLiteral "up one set"
				 */
				pointsWhereNoLiteralsAreFulfillable =
						pointsWhereNoLiteralsAreFulfillable.difference(toMoveFromNoToOne);
				pointsWhereOneLiteralIsFulfillable =
						pointsWhereOneLiteralIsFulfillable.union(toMoveFromNoToOne);
				pointsWhereOneLiteralIsFulfillable =
						pointsWhereOneLiteralIsFulfillable.difference(toMoveFromOneToTwo);
				pointsWhereTwoOrMoreLiteralsAreFulfillable =
						pointsWhereTwoOrMoreLiteralsAreFulfillable.union(toMoveFromOneToTwo);

				// if the current ClauseLiteral is the last ClauseLiteral, its unit points are exactly the ones that
				// moved from noFulfillableLiteral to OneFulfillableLiteral ..
				clauseLitToPotentialUnitPoints.put(cl, mDawgFactory.copyDawg(toMoveFromNoToOne));
				// ... however if we later find out for some of these points, that it is fulfilled somewhere else, we
				// have to remove it from the list.
				final Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> newClauseLitToPotentialUnitPoints =
						new HashMap<>();
				for (final Entry<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> en
						: clauseLitToPotentialUnitPoints.entrySet()) {
//					en.getValue().removeAll(toMoveFromOneToTwo);
					newClauseLitToPotentialUnitPoints.put(
							en.getKey(),
							en.getValue().difference(toMoveFromOneToTwo));
				}
				clauseLitToPotentialUnitPoints = newClauseLitToPotentialUnitPoints;
			} else {
				assert cl.isRefuted(decideStackBorder);
			}
		}

		//remove all empty dawgs from clauseLitToPotentialUnitPoints
		final Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> finalClauseLitToUnitPoints =
						new HashMap<>();
		for (final Entry<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> en : clauseLitToPotentialUnitPoints.entrySet()) {
			if (!en.getValue().isEmpty()) {
				finalClauseLitToUnitPoints.put(en.getKey(), en.getValue());
			}
		}

		assert EprHelpers.verifySortsOfPoints(pointsWhereNoLiteralsAreFulfillable, getVariables());
		assert EprHelpers.verifySortsOfPoints(pointsWhereOneLiteralIsFulfillable, getVariables());
		assert EprHelpers.verifySortsOfPoints(pointsWhereTwoOrMoreLiteralsAreFulfillable, getVariables());


		if (!pointsWhereNoLiteralsAreFulfillable.isEmpty()) {
			setPointsWhereNoLiteralsAreFulfillable(decideStackBorder, pointsWhereNoLiteralsAreFulfillable);
			setClauseState(decideStackBorder, EprClauseState.Conflict);
		} else if (!pointsWhereOneLiteralIsFulfillable.isEmpty()) {
			final UnitPropagationData upd = new UnitPropagationData(finalClauseLitToUnitPoints, mDawgFactory);
			setUnitPropagationData(decideStackBorder, upd);
			setClauseState(decideStackBorder, EprClauseState.Unit);
		} else {
			assert pointsWhereTwoOrMoreLiteralsAreFulfillable.supSetEq(pointsToConsider)
				&& pointsToConsider.supSetEq(pointsWhereTwoOrMoreLiteralsAreFulfillable)
					: "we found no conflict and no unit points, thus all non-fulfilled points must be fulfillable "
					+ "on two or more literals";
			setClauseState(decideStackBorder, EprClauseState.Normal);
		}
		return getClauseState(decideStackBorder);
	}

	private void setUnitPropagationData(final DecideStackLiteral decideStackBorder, final UnitPropagationData upd) {
		if (decideStackBorder == null) {
			mUnitPropagationData = upd;
		} else {
			mDecideStackBorderToUnitPropagationData.put(decideStackBorder, upd);
		}
	}


	private void setPointsWhereNoLiteralsAreFulfillable(final DecideStackLiteral decideStackBorder,
		final IDawg<ApplicationTerm, TermVariable> pointsWhereNoLiteralsAreFulfillable) {
		if (decideStackBorder == null) {
			mConflictPoints = pointsWhereNoLiteralsAreFulfillable;
		} else {
			mDecideStackBorderToConflictPoints.put(decideStackBorder, pointsWhereNoLiteralsAreFulfillable);
		}
	}

	private EprClauseState getClauseState(final DecideStackLiteral decideStackBorder) {
		if (decideStackBorder == null) {
			return mEprClauseState;
		} else {
			final EprClauseState res = mDecideStackBorderToClauseState.get(decideStackBorder);
			assert res != null;
			return res;
		}
	}

	private void setClauseState(final DecideStackLiteral decideStackBorder, final EprClauseState newState) {
		if (decideStackBorder == null) {
			mClauseStateIsDirty = false;
			mEprClauseState = newState;
		} else {
			mDecideStackBorderToClauseState.put(decideStackBorder, newState);
		}
	}


	public SortedSet<TermVariable> getVariables() {
		return mVariables;
	}

	public UnitPropagationData getUnitPropagationData() {
		assert mUnitPropagationData != null;
		final UnitPropagationData result = mUnitPropagationData;
		mUnitPropagationData = null;
		return result;
	}

	public boolean isUnit() {
		assert !mHasBeenDisposed;
		if (mClauseStateIsDirty) {
			return determineClauseState(null) == EprClauseState.Unit;
		}
		return mEprClauseState == EprClauseState.Unit;
	}

	public boolean isConflict() {
		assert !mHasBeenDisposed;
		if (mClauseStateIsDirty) {
			return determineClauseState(null) == EprClauseState.Conflict;
		}
		return mEprClauseState == EprClauseState.Conflict;
	}

	public IDawg<ApplicationTerm, TermVariable> getConflictPoints() {
		if (mClauseStateIsDirty) {
			determineClauseState(null);
		}
		assert isConflict();
		assert mConflictPoints != null : "this should have been set somewhere..";
		return mConflictPoints;
	}

	public Set<ClauseLiteral> getLiterals() {
		assert !mHasBeenDisposed;
		return mLiterals;
	}

	public List<Literal[]> computeAllGroundings(final List<TTSubstitution> allInstantiations) {
		final ArrayList<Literal[]> result = new ArrayList<>();
		for (final TTSubstitution sub : allInstantiations) {
			final ArrayList<Literal> groundInstList = getSubstitutedLiterals(sub);
			result.add(groundInstList.toArray(new Literal[groundInstList.size()]));
		}

		return result;
	}

	public List<Literal[]> computeAllGroundings(final HashSet<ApplicationTerm> constants) {

		final List<TTSubstitution> allInstantiations =
				EprHelpers.getAllInstantiations(getVariables(), constants);

		return computeAllGroundings(allInstantiations);
	}

	protected ArrayList<Literal> getSubstitutedLiterals(final TTSubstitution sub) {
		assert false : "TODO reimplement";
		return null;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("{");
		String comma = "";

		for (final ClauseLiteral cl : getLiterals()) {
			sb.append(comma);
			sb.append(cl.toString());
			comma = ", ";
		}

		sb.append("}");
		return sb.toString();
	}

	public Set<Clause> getGroundings(final IDawg<ApplicationTerm, TermVariable> groundingDawg) {
		if (mIsGround) {
			assert groundingDawg.getSignature().getNoColumns() == 0;
			return Collections.singleton(new Clause(mDpllLiterals.toArray(new Literal[mDpllLiterals.size()])));
		}


		assert groundingDawg.getColNames().equals(mVariables) : "signatures don't match";

		final Set<Clause> result = new HashSet<>();

		for (final List<ApplicationTerm> point : groundingDawg){
			final Set<Literal> groundLits = getGroundingForPoint(point).getDomain();

			result.add(new Clause(groundLits.toArray(new Literal[groundLits.size()])));
		}

		return result;
	}


	/**
	 * Obtains a grounding of the clause for one point.
	 * The point needs to be in the clause's signature.
	 * Also tracks which instantiation comes from which ClauseLiteral -- which is useful for observing if a factoring has occurred.
	 * @param point
	 * @return
	 */
	private BinaryRelation<Literal, ClauseLiteral> getGroundingForPoint(final List<ApplicationTerm> point) {
		final TTSubstitution sub = new TTSubstitution(mVariables, point);
		final Set<Literal> groundLits = new HashSet<>();
//		Map<ClauseEprQuantifiedLiteral, Literal> quantifiedLitToInstantiation
		final BinaryRelation<Literal, ClauseLiteral> instantiationToClauseLiteral =
				new BinaryRelation<>();
		for (final ClauseLiteral cl : getLiterals()) {
			if (cl instanceof ClauseEprQuantifiedLiteral) {
				final ClauseEprQuantifiedLiteral ceql = (ClauseEprQuantifiedLiteral) cl;
				final Term[] ceqlArgs = ceql.mArgumentTerms.toArray(new Term[ceql.mArgumentTerms.size()]);
				final TermTuple newTT = sub.apply(new TermTuple(ceqlArgs));
				assert newTT.getFreeVars().size() == 0;
				final EprPredicateAtom at = ceql.getEprPredicate().getAtomForTermTuple(
						newTT,
						mEprTheory.getTheory(),
						mEprTheory.getClausifier().getStackLevel(),
						ceql.getAtom().getSourceAnnotation());

				final Literal newLit = cl.getPolarity() ? at : at.negate();

				instantiationToClauseLiteral.addPair(newLit, ceql);
				groundLits.add(newLit);
			} else {
				instantiationToClauseLiteral.addPair(cl.getLiteral(), cl);
				groundLits.add(cl.getLiteral());
			}
		}
		return instantiationToClauseLiteral;
	}


	/**
	 * Checks if in the current decide state a factoring of this conflict clause is possible.
	 * If a factoring is possible, a factored clause is returned.
	 * Otherwise this clause is returned unchanged.
	 *
	 * @return A factored version of this clause or this clause.
	 */
	public EprClause factorIfPossible() {
		assert this.isConflict();

		for (final List<ApplicationTerm> cp : getConflictPoints()) {
			final BinaryRelation<Literal, ClauseLiteral> cpg = getGroundingForPoint(cp);

			for (final Literal groundLit : cpg.getDomain()) {
				final Set<ClauseLiteral> preGroundingClauseLits = cpg.getImage(groundLit);
				if (preGroundingClauseLits.size() == 1) {
					// no factoring occurred for that literal
					continue;
				}
				assert preGroundingClauseLits.size() > 1;
				/*
				 *  factoring occurred for that literal
				 *  that literal is a conflict grounding of this conflict epr clause
				 *  --> we can factor this conflict epr clause
				 */
				assert preGroundingClauseLits.size() == 2 : "TODO: deal with factoring for more than two literals";
				ClauseEprQuantifiedLiteral ceql = null;
				ClauseEprLiteral cel = null;
				for (final ClauseLiteral cl : preGroundingClauseLits) {
					assert cl instanceof ClauseEprLiteral;
					if (ceql == null && cl instanceof ClauseEprQuantifiedLiteral) {
						ceql = (ClauseEprQuantifiedLiteral) cl;
					} else if (cel == null &&
							(ceql != null || !(cl instanceof ClauseEprQuantifiedLiteral))) {
						cel = (ClauseEprLiteral) cl;
					}
				}
				assert cel != null && ceql != null && !cel.equals(ceql);


				mEprTheory.getLogger().debug("EPRDEBUG: (EprClause): factoring " + this);
				final EprClause factor = mEprTheory.getEprClauseFactory().getFactoredClause(ceql, cel);
				assert factor.isConflict() : "we only factor conflicts -- we should get a conflict out, too.";
				return factor;
			}
		}

		// when we can't factor, we just return this clause
		return this;
	}

	public boolean isUnitBelowDecisionPoint(final DecideStackDecisionLiteral dsdl) {
		final EprClauseState state = determineClauseState(dsdl);
		return state == EprClauseState.Unit;
	}

	public Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> getClauseLitToUnitPointsBelowDecisionPoint(
			final DecideStackDecisionLiteral dsdl) {
		final Map<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> res = mDecideStackBorderToClauseLitToUnitPoints.get(dsdl);
		assert res != null;
		return res;
	}
}
