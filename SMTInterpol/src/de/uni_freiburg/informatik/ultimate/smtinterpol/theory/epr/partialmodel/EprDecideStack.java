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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprEqualityPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseDpllLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.UnitPropagationData;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

/**
 * The decide stack for EPR is similar to the DPLL stack for DPLL(T). It contains entries for decisions and propagations
 * on EprPredicate objects. However each entry may change the value of the predicate at many positions, because a
 * quantified unit clause was propagated, or a decision was taken for more than one particular value.
 *
 * There are three types of items in the decide stack: EprGroundLiterals and ground equalities set by the DPLL engine
 * via setLiteral, propagations set by unit propagation of quantified clauses, and decisions produced in
 * computeConflictClause().
 *
 * When a new literal from the DPLL engine is asserted while we have a decision, we backtrack to the first decision
 * point.
 * 
 * @author Jochen Hoenicke
 *
 */
public class EprDecideStack {
	private final EprTheory mEprTheory;
	private final ArrayList<DecideStackEntry> mStack = new ArrayList<>();
	private final ScopedArrayList<EprClause> mClauses = new ScopedArrayList<>();
	private final ScopedHashSet<EprPredicate> mAllEprPredicates = new ScopedHashSet<>();
	private final ScopedArrayList<EprEqualityPredicate> mEprEqualities = new ScopedArrayList<>();

	public EprDecideStack(EprTheory theory) {
		mEprTheory = theory;
	}

	public void pushEntry(DecideStackEntry entry) {
		mStack.add(entry);
		entry.push(this);
	}

	public void backtrackToLiteral(Literal lit) {
		int stackTop = mStack.size();
		while (stackTop > 0) {
			DecideStackEntry entry = mStack.get(--stackTop);
			if (entry instanceof DecideStackGroundLiteral) {
				if (((DecideStackGroundLiteral) entry).getLiteral() == lit) {
					for (int i = mStack.size() - 1; i >= stackTop; i--) {
						mStack.remove(i).pop(this);
					}
					return;
				}
			}
		}
	}

	void explainConflict(Map<EprPredicate, HashSet<DawgState<ApplicationTerm, EprTheory.TriBool>>> conflict,
			List<Literal> groundClause) {
	}

	void resolveConflictOrUnit(EprClause clause, ClauseEprLiteral unitLiteral,
			DawgState<ApplicationTerm, Boolean> conflicts,
			Set<Literal> groundLits, Map<Pair<EprPredicate, Boolean>, Set<List<ApplicationTerm>>> eprLits) {
		// it is enough to extract one conflict, so get a ground instantiation.
		// TODO move to function
		List<DawgLetter<ApplicationTerm>> word = DawgFactory.getOneWord(conflicts);
		ApplicationTerm[] grounding = new ApplicationTerm[word.size()];
		for (int i = 0; i < word.size(); i++) {
			grounding[i] = word.get(i).isComplemented() ? null : word.get(i).getLetters().iterator().next();
		}

		for (ClauseLiteral lit : clause.getLiterals()) {
			if (lit instanceof ClauseDpllLiteral) {
				groundLits.add(((ClauseDpllLiteral) lit).getLiteral());
			} else if (lit == unitLiteral){
				// don't include the unit literal in the new conflict.
				continue;
			} else {
				ClauseEprLiteral eprLit = (ClauseEprLiteral) lit;
				ApplicationTerm[] instantiation = eprLit.getInstantiatedArguments(grounding);
				Pair<EprPredicate, Boolean> key = new Pair<>(eprLit.getEprPredicate(), eprLit.getPolarity());
				Set<List<ApplicationTerm>> prevWords = eprLits.get(key);
				if (prevWords == null) {
					prevWords = new HashSet<>();
					eprLits.put(key, prevWords);
				}
				prevWords.add(Arrays.asList(instantiation));
			}
		}
	}

	Clause explain(Set<Literal> groundClause, Map<Pair<EprPredicate, Boolean>, Set<List<ApplicationTerm>>> eprClause) {
		int stackPosition = mStack.size();
		while (!eprClause.isEmpty()) {
			DecideStackEntry entry = mStack.get(--stackPosition);

			if (entry instanceof DecideStackGroundLiteral) {
				// Check if the literal set by the DPLL engine is a valid explanation for one of the literals.
				Literal setLiteral = ((DecideStackGroundLiteral) entry).getLiteral();
				if (!(setLiteral.getAtom() instanceof EprGroundPredicateAtom)) {
					continue;
				}
				EprGroundPredicateAtom setAtom = (EprGroundPredicateAtom) setLiteral.getAtom();
				EprPredicate setPred = setAtom.getEprPredicate();
				Pair<EprPredicate, Boolean> key = new Pair<>(setPred, setAtom != setLiteral);
				Set<List<ApplicationTerm>> toExplainForLit = eprClause.get(key);
				if (toExplainForLit != null && toExplainForLit.remove(setAtom.getArgumentsAsWord())) {
					groundClause.add(setLiteral.negate());
					if (toExplainForLit.isEmpty()) {
						eprClause.remove(key);
					}
				}
			} else if (entry instanceof DecideStackPropagatedLiteral) {
				/*
				 * the propagated literal that was the root of the inconsistency has been popped its reason for
				 * propagation should be a conflict now instead of a unit resolve that conflict
				 */
				DecideStackPropagatedLiteral dsl = (DecideStackPropagatedLiteral) entry;
				DawgState<ApplicationTerm, EprTheory.TriBool> oldDawg = dsl.getOldDawg();
				ClauseEprLiteral propReason = dsl.getReasonClauseLit();
				// get all matching epr literals and remove them.
				Pair<EprPredicate, Boolean> key = new Pair<>(propReason.getEprPredicate(), !propReason.getPolarity());
				Set<List<ApplicationTerm>> toExplainForLit = eprClause.remove(key);
				if (toExplainForLit != null) {
					// we can safely iterate over the epr literals as we already removed them from the eprClause.
					Iterator<List<ApplicationTerm>> it = toExplainForLit.iterator();
					while (it.hasNext()) {
						List<ApplicationTerm> word = it.next();
						if (oldDawg.getValue(word) == EprTheory.TriBool.UNKNOWN) {
							// No earlier propagation contains the current conflict.
							// So this propagation needs to explain the conflict.
							assert dsl.getDawg().getValue(word) == 
									(propReason.getPolarity() ? EprTheory.TriBool.TRUE :EprTheory.TriBool.FALSE);
							it.remove();

							DawgState<ApplicationTerm, Boolean> litDawg = mEprTheory.getDawgFactory()
									.createSingletonSet(propReason.getEprPredicate().getTermVariablesForArguments(),
											word);
							DawgState<ApplicationTerm, Boolean> clauseDawg = propReason
									.litDawg2clauseDawg(litDawg);
							clauseDawg = mEprTheory.getDawgFactory().createIntersection(dsl.getClauseDawg(),
									clauseDawg);
							resolveConflictOrUnit(propReason.getClause(), propReason, clauseDawg, groundClause,
									eprClause);
						}
					}
					// we now have to insert the remaining epr literals again, but it can happen that we added
					// more literals in the mean time.  These do not have to be re-checked.
					Set<List<ApplicationTerm>> insertedLits = eprClause.get(key);
					if (insertedLits != null) {
						insertedLits.addAll(toExplainForLit);
					} else if (!toExplainForLit.isEmpty()) {
						eprClause.put(key, toExplainForLit);
					}
				}
			} else {
				throw new AssertionError();
			}
		}
		return new Clause(groundClause.toArray(new Literal[groundClause.size()]));
	}

	/**
	 * Explain a unit propagated literal or a conflict, which must be a EprGroundPredicateAtom. To explain a conflict
	 * call this with the last literal set in its negated form, as if you would just want to propagate the negated
	 * literal. This may only be called if there is no decision on the EPR stack. Otherwise it may not be possible to
	 * explain the conflict to the DPLL engine.
	 * 
	 * @param point
	 *            the dawg for the points where the unit literal or conflict happened.
	 * @param unitLiteral
	 *            the unit literal to explain, or null if a conflict should be explained
	 */
	Clause explainUnitLiteralOrConflict(EprClause clause, ClauseEprLiteral unitLiteral,
			DawgState<ApplicationTerm, Boolean> point) {
		HashSet<Literal> groundClause = new HashSet<>();
		HashMap<Pair<EprPredicate, Boolean>, Set<List<ApplicationTerm>>> eprClause = new HashMap<>();
		resolveConflictOrUnit(clause, unitLiteral, point, groundClause, eprClause);
		return explain(groundClause, eprClause);
	}

	Clause explainIrreflexivity(EprEqualityPredicate equality, DawgState<ApplicationTerm, Boolean> point) {
		HashSet<Literal> groundClause = new HashSet<>();
		HashMap<Pair<EprPredicate, Boolean>, Set<List<ApplicationTerm>>> eprClause = new HashMap<>();
		// it is enough to extract one conflict, so get a ground instantiation.
		// TODO move to function
		List<DawgLetter<ApplicationTerm>> word = DawgFactory.getOneWord(point);
		ApplicationTerm[] grounding = new ApplicationTerm[word.size()];
		for (int i = 0; i < word.size(); i++) {
			grounding[i] = word.get(i).isComplemented() ? null : word.get(i).getLetters().iterator().next();
		}
		Set<List<ApplicationTerm>> conflictSet = new HashSet<>();
		conflictSet.add(Arrays.asList(grounding));
		eprClause.put(new Pair<>(equality, Boolean.TRUE), conflictSet);
		return explain(groundClause, eprClause);
	}

	/**
	 * Explain a unit propagated literal or a conflict, which must be a EprGroundPredicateAtom. To explain a conflict
	 * call this with the last literal set in its negated form, as if you would just want to propagate the negated
	 * literal. This may only be called if there is no decision on the EPR stack. Otherwise it may not be possible to
	 * explain the conflict to the DPLL engine.
	 * 
	 * @param point
	 *            the dawg for the points where the unit literal or conflict happened.
	 * @param unitLiteral
	 *            the unit literal to explain, or null if a conflict should be explained
	 */
	Clause explainGroundUnit(Literal unit) {
		EprGroundPredicateAtom atom = (EprGroundPredicateAtom) unit.getAtom();
		HashSet<Literal> groundClause = new HashSet<>();
		HashMap<Pair<EprPredicate, Boolean>, Set<List<ApplicationTerm>>> eprClause = new HashMap<>();
		groundClause.add(unit);
		Set<List<ApplicationTerm>> wordSet = new HashSet<>();
		wordSet.add(atom.getArgumentsAsWord());
		eprClause.put(new Pair<>(atom.getEprPredicate(), unit != atom), wordSet);
		return explain(groundClause, eprClause);
	}

	public Clause setGroundEquality(CCEquality atom, boolean b) {
		// TODO Auto-generated method stub
		return null;
	}

	public Clause setEprGroundLiteral(Literal literal) {
		EprGroundPredicateAtom atom = (EprGroundPredicateAtom) literal.getAtom();
		EprPredicate pred = atom.getEprPredicate();
		if (pred.getDawg().getValue(atom.getArgumentsAsWord()) == 
				(literal == atom ? EprTheory.TriBool.FALSE : EprTheory.TriBool.TRUE)) {
			// we have a conflict to a previously set state
			return explainGroundUnit(literal.negate());
		}
		DecideStackGroundLiteral dsgl = new DecideStackGroundLiteral(literal);
		pushEntry(dsgl);
		return null;
	}

	public Clause doPropagations() {
		boolean changed = true;
		while (changed) {
			changed = false;
			for (EprEqualityPredicate equality : mEprEqualities) {
				DawgState<ApplicationTerm, Boolean> conflicts = equality.getIrreflexivity();
				if (!DawgFactory.isEmpty(conflicts)) {
					return explainIrreflexivity(equality, conflicts);
				}
			}
			for (EprClause eprClause : mClauses) {
				if (eprClause.isConflict()) {
					DawgState<ApplicationTerm, Boolean> conflicts = eprClause.getConflictPoints();
					return explainUnitLiteralOrConflict(eprClause, null, conflicts);
				}
				if (eprClause.isUnit()) {
					UnitPropagationData upd = eprClause.getUnitPropagationData();
					for (DecideStackEntry dse : upd.getQuantifiedPropagations()) {
						mEprTheory.getLogger().debug("EPR Propagating: %s", dse);
						pushEntry(dse);
						changed = true;
					}
				}
			}
		}
		return null;
	}

	public Clause eprDpllLoop() {
		// TODO Auto-generated method stub
		return null;
	}

	public Clause createEprClause(Set<Literal> clauseLiterals) {
		final EprClause newClause = mEprTheory.getEprClauseFactory().getEprClause(clauseLiterals);

		mEprTheory.getLogger().debug("EPRDEBUG: (EprClauseManager) creating new EprClause: " + newClause);
		mClauses.add(newClause);
		return null;
	}

	public void addNewEprPredicate(final EprPredicate pred) {
		if (pred instanceof EprEqualityPredicate) {
			mEprEqualities.add((EprEqualityPredicate) pred);
		}
		mAllEprPredicates.add(pred);
	}

	public void push() {
		mClauses.beginScope();
		mAllEprPredicates.beginScope();
		mEprEqualities.beginScope();
	}

	public void pop() {
		mClauses.endScope();
		mAllEprPredicates.endScope();
		mEprEqualities.endScope();
	}

}
