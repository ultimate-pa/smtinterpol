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

package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.SortSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAnnotation.RuleKind;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm.Parent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ArrayQueue;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * Solver for the data type theory.
 *
 * This theory understands relations between data types, their constructors and selectors.
 * It propagates new equalities between data type terms as well as the arguments of their constructors.
 * It also detects all conflicts in these relations. It uses the equality graph of the CClosure class.
 *
 * @author Moritz Mohr
 *
 */
public class DataTypeTheory implements ITheory {

	private final Clausifier mClausifier;
	private final CClosure mCClosure;
	private final Theory mTheory;
	/**
	 * The list of cc-term pairs, whose equality we need to prpagate
	 */
	private final ArrayDeque<SymmetricPair<CCTerm>>mPendingEqualities = new ArrayDeque<>();
	/**
	 * A map from selector name to the matching constructor.
	 * This is used as a cache for {@link #getConstructor(ApplicationTerm)}
	 */
	private final LinkedHashMap<String, Constructor> mSelectorMap = new LinkedHashMap<>();
	/**
	 * Collect all created terms to check after a backtrack if their equalities are still valid.
	 */
	private ArrayQueue<CCTerm> mRecheckOnBacktrack = new ArrayQueue<>();
	/**
	 * This a cache for {@link #isInfinite(Sort, LinkedHashSet)}
	 */
	private final LinkedHashMap<Sort, Boolean> mInfinityMap = new LinkedHashMap<>();
	/**
	 * This maps from a pair of equal terms to a list of pairs of equal terms.
	 * The equalities of the term pairs in the list are the reason for the equality of the key pair
	 * and are used to generate the unit clause.
	 */
	private final LinkedHashMap<SymmetricPair<CCTerm>, DataTypeLemma> mEqualityReasons = new LinkedHashMap<>();

	public DataTypeTheory(final Clausifier clausifier, final Theory theory, final CClosure cclosure) {
		mClausifier = clausifier;
		mCClosure = cclosure;
		mTheory = theory;
	}

	/**
	 * add a new equality between two terms to be propagated.
	 * @param eq the terms that are equal.
	 * @param reason the terms which are needed for the unit clause generation.
	 */
	public void addPendingEquality(final SymmetricPair<CCTerm> eq, final DataTypeLemma reason) {
		if (eq.getFirst() == eq.getSecond() || eq.getFirst().mRepStar == eq.getSecond().mRepStar) {
			return;
		}
		mPendingEqualities.add(eq);
		mEqualityReasons.put(eq, reason);
	}

	@Override
	public Clause startCheck() {
		return null;
	}

	@Override
	public void endCheck() {
	}

	@Override
	public Clause setLiteral(final Literal literal) {
		return null;
	}

	@Override
	public void backtrackLiteral(final Literal literal) {
	}

	@Override
	public Clause checkpoint() {

		//Visit all ((_ is CONS) u) terms that are true and try to apply rule 3 or 9 on them
		final CCTerm trueRep = mCClosure.getCCTermRep(mTheory.mTrue);
		final LinkedHashMap<CCTerm, LinkedHashSet<CCAppTerm>> visited = new LinkedHashMap<>();
		for (final CCTerm t : trueRep.mMembers) {
			if (t instanceof CCAppTerm && t.mFlatTerm instanceof ApplicationTerm) {
				final ApplicationTerm at = (ApplicationTerm) t.mFlatTerm;
				final CCAppTerm ccat = (CCAppTerm) t;
				if (at.getFunction().getName() == "is") {
					if (!visited.containsKey(ccat.mArg.mRepStar)) {
						visited.put(ccat.mArg.mRepStar, new LinkedHashSet<>());
						visited.get(ccat.mArg.mRepStar).add(ccat);
						Rule3((CCAppTerm) t);
					} else {
						/*
						 * Rule 9:
						 * Since a constructor can't be equal to another constructor,
						 * there must not be multiple true is functions that test for different constructors.
						 */
						for (final CCAppTerm visitor : visited.get(ccat.mArg.mRepStar)) {
							if (visitor.getFunc().mParentPosition != ccat.getFunc().mParentPosition) {
								final CongruencePath cpIs = new CongruencePath(mCClosure);
								final CongruencePath cpArg = new CongruencePath(mCClosure);
								cpIs.computePath(visitor, ccat);
								cpArg.computePath(ccat.mArg, visitor.mArg);
								final HashSet<Literal> lits = new HashSet<>();
								lits.addAll(cpIs.mAllLiterals);
								lits.addAll(cpArg.mAllLiterals);
								final Literal[] negLits = new Literal[lits.size()];
								int i = 0;
								for (final Literal l : lits) {
									negLits[i++] = l.negate();
								}
								mClausifier.getLogger().debug("Conflict: Rule 9");
								return new Clause(negLits);
							}
						}
					}
				}
			}
		}

		// collect all cc-terms that have a "is" function as parent which is equal to false
		final LinkedHashMap<CCTerm, LinkedHashSet<CCTerm>> falseIsFuns = new LinkedHashMap<>();
		final CCTerm falseRep = mCClosure.getCCTermRep(mTheory.mFalse);
		for (final CCTerm cct : falseRep.mMembers) {
			if (cct.mFlatTerm instanceof ApplicationTerm && ((ApplicationTerm) cct.mFlatTerm).getFunction().getName().equals("is")) {
				falseIsFuns.putIfAbsent(((CCAppTerm)cct).mArg.mRepStar, new LinkedHashSet<>());
				falseIsFuns.get(((CCAppTerm)cct).mArg.mRepStar).add(cct);
			}
		}

		for (final CCTerm cct : falseIsFuns.keySet()) {
			final DataType dt = (DataType) cct.mFlatTerm.getSort().getSortSymbol();
			if (falseIsFuns.get(cct).size() >= dt.getConstructors().length) {
				final LinkedHashMap<String, CCTerm> isIndices = new LinkedHashMap<>();
				for (final CCTerm isFun : falseIsFuns.get(cct)) {
					isIndices.put(((ApplicationTerm) isFun.mFlatTerm).getFunction().getIndices()[0], isFun);
				}
				/*
				 * Rule 6:
				 * Every data type term must be equal to a constructor.
				 * Thus, not all "is" functions may be false.
				 */
				if (isIndices.size() == dt.getConstructors().length) {
					final HashSet<Literal> lits = new HashSet<>();
					for (final CCTerm isFun : isIndices.values()) {
						final CongruencePath cp = new CongruencePath(mCClosure);
						cp.computePath(isFun, falseRep);
						cp.computePath(((CCAppTerm)isFun).mArg, cct);
						lits.addAll(cp.mAllLiterals);
					}
					final Literal[] negLits = new Literal[lits.size()];
					int i = 0;
					for (final Literal l : lits) {
						negLits[i++] = l.negate();
					}
					mClausifier.getLogger().debug("Conflict: Rule 6");
					return new Clause(negLits);
				}
			}
		}

		final LinkedHashSet<CCTerm> DTReps = new LinkedHashSet<>();
		for (final CCTerm ct : mCClosure.mAllTerms) {
			if (ct == ct.mRep && ct.mFlatTerm != null && ct.mFlatTerm.getSort().getSortSymbol().isDatatype()) {
				DTReps.add(ct);
			}
		}

		for (final CCTerm ct : DTReps) {
			Rule4(ct);
			Rule5(ct);

			final Clause cl = Rule8(ct);
			if (cl != null) {
				mClausifier.getLogger().debug("Conflict: Rule 8");
				return cl;
			}
		}


		return null;
	}

	@Override
	public Clause computeConflictClause() {
		// check for cycles (Rule7)
		/*
		 * Rule 7:
		 * Constructor arguments must not contain the constructor term itself, so we need to check
		 * if there is any cycle in the equality graph.
		 * To do this, we do a depth-first-search over the graph, noting terms (visitedOnPath) already visited
		 * to detect a cycle.
		 */

		// Remember all visited terms in this set to avoid searching the same sub tree more than once.
		final LinkedHashSet<CCTerm> visited = new LinkedHashSet<>();


		final Deque<CCTerm> path = new ArrayDeque<>();
		final Set<CCTerm> visitedOnPath = new LinkedHashSet<>();
		final Deque<CCTerm> todo = new ArrayDeque<>();
		final Map<CCTerm, SymmetricPair<CCTerm>> argConsPairs = new LinkedHashMap<>();
		final Map<CCTerm, CCAppTerm> possibleCons = new LinkedHashMap<>();

		for (final CCTerm start : mCClosure.mAllTerms) {
			if (start == start.mRepStar && start.mFlatTerm != null && start.mFlatTerm.getSort().getSortSymbol().isDatatype()) {
				todo.push(start);

				while (!todo.isEmpty()) {
					final CCTerm ct = todo.pop();
					final CCTerm rep = ct.mRepStar;

					if (visited.contains(rep)) {
						if (path.peek() == rep) {
							path.pop();
							visitedOnPath.remove(rep);
						}
						continue;
					}

					final ArrayDeque<CCTerm> children = new ArrayDeque<>();
					final CCTerm cons = getAllDataTypeChildren(rep, children);

					if (!children.isEmpty()) {
						path.push(rep);
						visitedOnPath.add(rep);
						todo.push(rep);

						if (cons == null || ((ApplicationTerm)cons.mFlatTerm).getFunction().getName().equals("is")) {
							possibleCons.put(rep, (CCAppTerm) cons);
							argConsPairs.put(rep, new SymmetricPair<>(ct, null));
						} else {
							argConsPairs.put(rep, new SymmetricPair<>(ct, cons));
						}

						for (final CCTerm c : children) {
							if (visitedOnPath.contains(c.mRepStar)) {
								// one of the children is already on the path so we found a cycle
								return buildCycleConflict(c, path, argConsPairs, possibleCons);
							}
							todo.push(c);
						}
					}
					visited.add(rep);
				}
			}
		}
		return null;
	}

	/**
	 * This functions searches all data type children of a given term.
	 * This means, if there is a constructor term, that it is equal to the given term, it finds all of its argument with a data type sort.
	 * If there is no such constructor term, it searches for applications of selector term on the equality class and returns all selector
	 * term, which could be valid applications.
	 *
	 * @param rep The representative of the equality class.
	 * @param children An empty list, which will be filled with children if there are any.
	 * @return The constructor term which is equal to rep, if there is none, it returns a true "is" function for this equality class,
	 * if there is also none, it returns null.
	 */
	private CCTerm getAllDataTypeChildren(CCTerm rep, final ArrayDeque<CCTerm> children) {
		CCTerm consResult = null;
		rep = rep.mRepStar;
		for (final CCTerm mem : rep.mMembers) {
			if (mem.mFlatTerm instanceof ApplicationTerm && ((ApplicationTerm)mem.mFlatTerm).getFunction().isConstructor()) {
				for (final Term arg : ((ApplicationTerm)mem.mFlatTerm).getParameters()) {
					if (arg.getSort().getSortSymbol().isDatatype()) {
						children.add(mClausifier.getCCTerm(arg));
					}
				}
				consResult = mem;
				break;
			}
		}

		if (consResult == null) {
			final CCTerm trueRep = mClausifier.getCCTerm(mTheory.mTrue).mRepStar;
			final Set<CCAppTerm> selectors = new LinkedHashSet<>();
			final Set<String> rightSelectors = new LinkedHashSet<>();
			final Set<String> falseSelectors = new LinkedHashSet<>();
			CCParentInfo pInfo = rep.mCCPars;
			while (pInfo != null) {
				if (pInfo.mCCParents != null && pInfo.mCCParents.iterator().hasNext()) {
					final CCAppTerm p = pInfo.mCCParents.iterator().next().getData();
					if (p.mFlatTerm instanceof ApplicationTerm) {
						final FunctionSymbol pFun = ((ApplicationTerm) p.mFlatTerm).getFunction();
						if (pFun.isSelector() && p.mFlatTerm.getSort().getSortSymbol().isDatatype()) {
							selectors.add(p);
						} else if (pFun.getName().equals("is")) {
							final Constructor c = ((DataType)rep.mFlatTerm.getSort().getSortSymbol()).findConstructor(pFun.getIndices()[0]);
							if (p.mRepStar == trueRep) {
								rightSelectors.addAll(Arrays.asList(c.getSelectors()));
								consResult = p;
							} else {
								falseSelectors.addAll(Arrays.asList(c.getSelectors()));
							}
						}
					}
				}
				pInfo = pInfo.mNext;
			}

			if (!rightSelectors.isEmpty()) {
				for (final CCAppTerm s : selectors) {
					if (rightSelectors.contains(((ApplicationTerm)s.mFlatTerm).getFunction().getName())) {
						children.add(s);
					}
				}
			} else {
				for (final CCAppTerm s : selectors) {
					if (!falseSelectors.contains(((ApplicationTerm)s.mFlatTerm).getFunction().getName())) {
						children.add(s);
					}
				}
			}

		}

		return consResult;
	}

	/**
	 * This function builds the conflict clause for a path that contains a cycle.
	 * If there is one equality class on the path for which it is not sure whether it is the constructor in question,
	 * it builds an "is" term to let the dpll engine decide.
	 *
	 * @param currentTerm The term whose equality class already appeared on the path.
	 * @param path The list of representatives of equality classes in order of visit.
	 * @param argConsPairs A table of representatives of equality classes
	 *  which point to the argument of the preceding constructor and the constructor which argument is next in the path.
	 * @param possibleCons A collection of representatives of equality classes that have no constructor function as member, but could have.
	 * @return a conflict clause for the cyclic part of path, if there is for all equality classes in path a constructor term in the equality class or a true "is" term of the equality class.
	 * If for one equality class there is no constructor or "is" term, it returns null.
	 */
	private Clause buildCycleConflict(final CCTerm currentTerm, final Deque<CCTerm> path, final Map<CCTerm, SymmetricPair<CCTerm>> argConsPairs, final Map<CCTerm, CCAppTerm> possibleCons) {
		final Set<Literal> literals = new HashSet<>();
		final CCTerm rep = currentTerm.mRepStar;
		CCTerm lastCt = currentTerm;
		final CongruencePath cp = new CongruencePath(mCClosure);
		while (!path.isEmpty()) {
			final CCTerm pathRep = path.pop();
			SymmetricPair<CCTerm> pair = argConsPairs.get(pathRep);

			// if it is not sure that pathRep is the matching constructor to the selector (lastCT)
			// build an is-function
			if (possibleCons.containsKey(pathRep)) {
				final CCAppTerm isFun = possibleCons.get(pathRep);
				if (isFun == null) {
					final String selName = ((ApplicationTerm) lastCt.mFlatTerm).getFunction().getName();
					final Sort repSort = pathRep.mFlatTerm.getSort();
					for (final Constructor c : ((DataType) repSort.getSortSymbol()).getConstructors()) {
						for (final String s : c.getSelectors()) {
							if (s.equals(selName)) {
								final Term isTerm = mTheory.term(mTheory.getFunctionWithResult("is", new String[] {c.getName()}, null, repSort), pair.getFirst().mFlatTerm);
								mClausifier.createCCTerm(isTerm, SourceAnnotation.EMPTY_SOURCE_ANNOT);
								return null;
							}
						}
					}
					mClausifier.getLogger().error("Should have found the matching constructor to %s", selName);
					return null;
				} else {
					cp.computePath(isFun, mClausifier.getCCTerm(mTheory.mTrue));
				}
			}


			// pair.getSecond() == null, means lastCt must be a selector application on rep
			if (pair.getSecond() == null) {
				pair = new SymmetricPair<>(pair.getFirst(), ((CCAppTerm)lastCt).mArg);
			}

			if (rep == pathRep) {
				cp.computePath(currentTerm, pair.getSecond());
				literals.addAll(cp.mAllLiterals);
				break;
			}
			cp.computePath(pair.getFirst(), pair.getSecond());
			literals.addAll(cp.mAllLiterals);
			lastCt = pair.getFirst();
		}
		final Literal[] negLits = new Literal[literals.size()];
		int i = 0;
		for (final Literal l : literals) {
			negLits[i++] = l.negate();
		}
		mClausifier.getLogger().debug("Found Cycle: %s", literals);
		return new Clause(negLits);
	}

	@Override
	public Literal getPropagatedLiteral() {
		if (!mPendingEqualities.isEmpty()) {
			final SymmetricPair<CCTerm> eqPair = mPendingEqualities.poll();
			return mCClosure.createEquality(eqPair.getFirst(), eqPair.getSecond(), false);
		}
		return null;
	}

	@Override
	public Clause getUnitClause(final Literal literal) {
		final CCEquality eq = (CCEquality) literal;

		final DataTypeLemma lemma = mEqualityReasons.get(new SymmetricPair<>(eq.getLhs(), eq.getRhs()));
		final boolean isProofEnabled = mClausifier.getEngine().isProofGenerationEnabled();
		final CongruencePath cp = new CongruencePath(mCClosure);
		return cp.computeDTLemma(eq, lemma, isProofEnabled);
	}

	@Override
	public Literal getSuggestion() {
		return null;
	}

	@Override
	public int checkCompleteness() {
		return 0;
	}

	@Override
	public void printStatistics(final LogProxy logger) {
	}

	@Override
	public void dumpModel(final LogProxy logger) {
	}

	@Override
	public void increasedDecideLevel(final int currentDecideLevel) {
	}

	@Override
	public void decreasedDecideLevel(final int currentDecideLevel) {
	}

	@SuppressWarnings("unchecked")
	@Override
	public Clause backtrackComplete() {
		// if we constructed new terms, their equalities have been removed in the backtracking process,
		// so we need to check if they are still valid.
		mPendingEqualities.clear();
		final ArrayQueue<CCTerm> newRecheckOnBacktrack = new ArrayQueue<>();
		while (!mRecheckOnBacktrack.isEmpty()) {
			ApplicationTerm constructor = null;
			final CCTerm checkTerm = mRecheckOnBacktrack.poll();
			for (final CCTerm ct : ((CCAppTerm) checkTerm).mArg.mRepStar.mMembers) {
				if (ct.mFlatTerm instanceof ApplicationTerm && ((ApplicationTerm) ct.mFlatTerm).getFunction().isConstructor()) {
					constructor = (ApplicationTerm) ct.mFlatTerm;
					break;
				}
			}
			if (constructor == null) {
				continue;
			}
			final SymmetricPair<CCTerm> reasonPair =
					new SymmetricPair<>(((CCAppTerm) checkTerm).getArg(), mClausifier.getCCTerm(constructor));
			SymmetricPair<CCTerm>[] reason;
			if (reasonPair.getFirst() != reasonPair.getSecond()) {
				reason = new SymmetricPair[] { reasonPair };
			} else {
				reason = new SymmetricPair[0];
			}
			if (((ApplicationTerm) checkTerm.mFlatTerm).getFunction().isSelector()) {
				final String selName = ((ApplicationTerm) checkTerm.mFlatTerm).getFunction().getName();
				final Constructor c = mSelectorMap.get(selName);
				assert c.getName().equals(constructor.getFunction().getName());
				final DataTypeLemma lemma = new DataTypeLemma(RuleKind.DT_TESTER, reason);
				for (int i = 0; i < c.getSelectors().length; i++) {
					if (selName.equals(c.getSelectors()[i])) {
						final CCTerm arg = mClausifier.getCCTerm(constructor.getParameters()[i]);
						if (arg.mRepStar != checkTerm.mRepStar) {
							addPendingEquality(new SymmetricPair<>(arg, checkTerm), lemma);
						}
						newRecheckOnBacktrack.add(checkTerm);
					}
				}
			} else {
				if (constructor.getFunction().getName().equals(((ApplicationTerm) checkTerm.mFlatTerm).getFunction().getIndices()[0])) {
					final CCTerm ccTrue = mClausifier.getCCTerm(mTheory.mTrue);
					final DataTypeLemma lemma = new DataTypeLemma(RuleKind.DT_PROJECT, reason);
					if (ccTrue.mRepStar != checkTerm.mRepStar) {
						addPendingEquality(new SymmetricPair<>(checkTerm, mClausifier.getCCTerm(mTheory.mTrue)), lemma);
					}
					newRecheckOnBacktrack.add(checkTerm);
				}
			}
		}
		mRecheckOnBacktrack = newRecheckOnBacktrack;
		return null;
	}

	@Override
	public void backtrackAll() {
	}

	@Override
	public void restart(final int iteration) {
	}

	@Override
	public void removeAtom(final DPLLAtom atom) {
	}

	@Override
	public void push() {
	}

	@Override
	public void pop() {
		mInfinityMap.clear();
	}

	@Override
	public Object[] getStatistics() {
		return new Object[] { ":DT" };
	}

	// TODO: rename
	/**
	 * Rule 3 checks if the argument of the isTerm has an application for every
	 * selector function and if so, builds a constructor term based on these selector functions.
	 * @param isTerm a "is" function term equal to true.
	 */
	private void Rule3(final CCAppTerm isTerm) {
		// check if there is already a constructor application equal to the argument
		final ApplicationTerm at = (ApplicationTerm) isTerm.mFlatTerm;
		final Term arg = at.getParameters()[0];

		//CCTerm argRep = mCClosure.getCCTermRep(arg);
		final CCTerm argRep = isTerm.mArg.mRepStar;
		final String consName = at.getFunction().getIndices()[0];
		if (argRep == null) {
			return;
		}
		for (final CCTerm mt : argRep.mMembers) {
			if (mt.mFlatTerm instanceof ApplicationTerm) {
				final ApplicationTerm mat = (ApplicationTerm) mt.mFlatTerm;
				final String matName = mat.getFunction().getName();
				if (matName.equals(consName)) {
					return;
				}
			}
		}

		// check if there are all selector applications on the eq class
		final DataType dt = (DataType) at.getFunction().getParameterSorts()[0].getSortSymbol();
		final Constructor c = dt.findConstructor(consName);

		final LinkedHashMap<String, Term> selectorApps = new LinkedHashMap<>();
		for (final String s : c.getSelectors()) {
			selectorApps.put(s, null);
		}

		if (selectorApps.size() > 0) {
			CCParentInfo argParInfo = argRep.mCCPars;
			while (argParInfo != null) {
				if (argParInfo.mCCParents != null) {
					for (final Parent p : argParInfo.mCCParents) {
						if (p.getData().mFlatTerm instanceof ApplicationTerm) {
							final String parFunName = ((ApplicationTerm) p.getData().mFlatTerm).getFunction().getName();
							if (selectorApps.containsKey(parFunName)) {
								selectorApps.put(parFunName, mTheory.term(parFunName, new Term[] {arg}));
							}
						}
					}
				}
				argParInfo = argParInfo.mNext;
			}
		}

		if (selectorApps.containsValue(null)) {
			return;
		}

		// create a new constructor application like C(s1(x), s2(x), ..., sm(x))

		final Term consTerm = mTheory.term(consName, selectorApps.values().toArray(new Term[selectorApps.values().size()]));
		final CCTerm consCCTerm = mClausifier.createCCTerm(consTerm, SourceAnnotation.EMPTY_SOURCE_ANNOT);
		final SymmetricPair<CCTerm> eq = new SymmetricPair<>(argRep, consCCTerm);
		final ArrayList<SymmetricPair<CCTerm>> reason = new ArrayList<>();
		if (arg != argRep.mFlatTerm) {
			reason.add(new SymmetricPair<>(mClausifier.getCCTerm(arg), argRep));
		}
		reason.add(new SymmetricPair<>(isTerm, mClausifier.getCCTerm(mTheory.mTrue)));
		@SuppressWarnings("unchecked")
		final DataTypeLemma lemma = new DataTypeLemma(RuleKind.DT_CONSTRUCTOR,
				reason.toArray(new SymmetricPair[reason.size()]));
		addPendingEquality(eq, lemma);

	}

	/**
	 * Rule 4 checks for a term if all missing selector function applications are of a finite sort
	 * and if so, builds them.
	 *
	 * @param ccterm a term with DataType sort.
	 */
	private void Rule4(final CCTerm ccterm) {
		final LinkedHashSet<String> exisitingSelectors = findAllSelectorApplications(ccterm);

		final SortSymbol sym = ccterm.mFlatTerm.getSort().getSortSymbol();
		for (final Constructor c : ((DataType) sym).getConstructors()) {
			// check if only selectors with finite return sort are missing and build them
			boolean noInfSel = true;
			final LinkedHashSet<String> neededSelectors = new LinkedHashSet<>();
			for (int i = 0; i < c.getSelectors().length; i++) {
				if (!exisitingSelectors.contains(c.getSelectors()[i])) {
					if (!c.getArgumentSorts()[i].getSortSymbol().isDatatype() || isInfinite(c.getArgumentSorts()[i])) {
						noInfSel = false;
						break;
					} else {
						neededSelectors.add(c.getSelectors()[i]);
					}
				}
			}
			if (noInfSel) {
				// build selectors
				for (final String sel : neededSelectors) {
					mRecheckOnBacktrack.add(mClausifier.createCCTerm(mTheory.term(mTheory.getFunctionSymbol(sel), ccterm.getFlatTerm()), SourceAnnotation.EMPTY_SOURCE_ANNOT));
				}
			}
		}
	}

	/**
	 * Rule 5 constructs an "is" term if there is a function application for every selector
	 * of the tested constructor on the given term.
	 *
	 * @param ccterm
	 */
	private void Rule5(final CCTerm ccterm) {
		final LinkedHashSet<String> selApps = findAllSelectorApplications(ccterm);
		final SortSymbol sym = ccterm.mFlatTerm.getSort().getSortSymbol();

		// check if there is already a constructor
		for (final CCTerm mem : ccterm.mMembers) {
			if (mem.mFlatTerm instanceof ApplicationTerm && ((ApplicationTerm)mem.mFlatTerm).getFunction().isConstructor()) {
				return;
			}
		}

		for (final Constructor c : ((DataType) sym).getConstructors()) {
			if (selApps.containsAll(Arrays.asList(c.getSelectors()))) {
				final FunctionSymbol isFs = mTheory.getFunctionWithResult("is", new String[] {c.getName()}, null, new Sort[] {ccterm.getFlatTerm().getSort()});
				final Term isTerm = mTheory.term(isFs, ccterm.mFlatTerm);
				if (mClausifier.getCCTerm(isTerm) == null) {
					mRecheckOnBacktrack.add(mClausifier.createCCTerm(isTerm, SourceAnnotation.EMPTY_SOURCE_ANNOT));
				}
			}
		}
	}

	/**
	 * Rule 8 checks for a given term if its equality class contains more than one constructor.
	 * If the constructor functions are equal, we need to propagate the equalities of their arguments,
	 * else we found a conflict.
	 * @param ccterm the term to check.
	 * @return The conflict clause if a conflict is found, else null.
	 */
	private Clause Rule8(final CCTerm ccterm) {
		ApplicationTerm consAt = null;
		CCTerm consCCTerm = null;
		for (final CCTerm mem : ccterm.mMembers) {
			if (mem.mFlatTerm instanceof ApplicationTerm && ((ApplicationTerm) mem.mFlatTerm).getFunction().isConstructor()) {
				final ApplicationTerm memAt = (ApplicationTerm) mem.getFlatTerm();
				if (consAt == null) {
					consAt = memAt;
					consCCTerm = mClausifier.getCCTerm(consAt);
					continue;
				}
				if (memAt.getFunction() == consAt.getFunction()) {
					for (int i = 0; i < memAt.getParameters().length; i++) {
						final CCTerm memArg = mClausifier.getCCTerm(memAt.getParameters()[i]);
						final CCTerm consArg = mClausifier.getCCTerm(consAt.getParameters()[i]);
						if (memArg.mRepStar != consArg.mRepStar) {
							final SymmetricPair<CCTerm> eqPair = new SymmetricPair<>(memArg, consArg);
							@SuppressWarnings("unchecked")
							final SymmetricPair<CCTerm>[] reason = new SymmetricPair[] {
									new SymmetricPair<>(consCCTerm, mem) };
							final DataTypeLemma lemma = new DataTypeLemma(RuleKind.DT_INJECTIVE, reason);
							addPendingEquality(eqPair, lemma);
						}
					}
				} else {
					final CongruencePath cp = new CongruencePath(mCClosure);
					cp.computePath(mem, consCCTerm);
					final Literal[] lits = new Literal[cp.mAllLiterals.size()];
					int i = 0;
					for (final Literal l : cp.mAllLiterals) {
						lits[i++] = l.negate();
					}
					return new Clause(lits);
				}
			}
		}
		return null;
	}

	/**
	 * Search the parents of ccterm for selector function applications.
	 *
	 * @param ccterm
	 * @return a map from selector name to the specific selector function application.
	 */
	private LinkedHashSet<String> findAllSelectorApplications(final CCTerm ccterm) {
		final LinkedHashSet<String> selApps = new LinkedHashSet<>();
		CCParentInfo parInfo = ccterm.mRepStar.mCCPars;
		while (parInfo != null) {
			if (parInfo.mCCParents != null && !parInfo.mCCParents.isEmpty()) {
					final Parent p = parInfo.mCCParents.iterator().next();
					final ApplicationTerm pAt = (ApplicationTerm) p.getData().getFlatTerm();
					if (pAt != null && pAt.getFunction().isSelector()) {
						selApps.add(pAt.getFunction().getName());
					}
			}
			parInfo = parInfo.mNext;
		}
		return selApps;
	}

	/**
	 * This function determines if a given sort is infinite or not.
	 *
	 * @param sort the sort in question.
	 * @return True if sort is infinite else False
	 */
	private boolean isInfinite(final Sort sort) {
		final Boolean cacheVal = mInfinityMap.get(sort);
		if (cacheVal != null) {
			return cacheVal;
		}
		final ArrayDeque<Sort> todo = new ArrayDeque<>();
		final Set<Sort> dependent = new LinkedHashSet<>();
		todo.push(sort);
		todo_loop: while (!todo.isEmpty()) {
			final Sort currSort = todo.pop();
			final Set<Sort> undecided = new LinkedHashSet<>();
			if (currSort.getSortSymbol().isDatatype()) {
				for (final Constructor c : ((DataType)currSort.getSortSymbol()).getConstructors()) {
					for (final Sort argSort : c.getArgumentSorts()) {
						final Boolean cv = mInfinityMap.get(argSort);
						if (cv != null) {
							if (cv == true) {
								mInfinityMap.put(currSort, true);
								dependent.remove(currSort);
								continue todo_loop;
							}
						} else if (dependent.contains(argSort)) {
							mInfinityMap.put(currSort, true);
							dependent.remove(currSort);
							continue todo_loop;
						} else {
							undecided.add(argSort);
						}
					}
				}
				if (!undecided.isEmpty()) {
					todo.push(currSort);
					dependent.add(currSort);
					for (final Sort s: undecided) {
						todo.push(s);
					}
				} else {
					mInfinityMap.put(currSort, false);
					dependent.remove(currSort);
				}
			} else if (currSort.getSortSymbol().isNumeric()) {
				mInfinityMap.put(currSort, true);
			} else {
				mInfinityMap.put(currSort, false);
			}
		}

		return mInfinityMap.get(sort);
	}

	/**
	 * Find the corresponding constructor to the given selector function.
	 *
	 * @param selector
	 * @return The constructor for which "selector" is a valid selector function.
	 */
	private Constructor getConstructor(final ApplicationTerm selector) {
		if (!selector.getFunction().isSelector()) {
			return null;
		}

		final String selName = selector.getFunction().getName();
		if (mSelectorMap.containsKey(selector.getFunction().getName())) {
			return mSelectorMap.get(selector.getFunction().getName());
		}

		for (final Constructor c : ((DataType)selector.getParameters()[0].getSort().getSortSymbol()).getConstructors()) {
			for (final String s : c.getSelectors()) {
				if (s.equals(selName)) {
					mSelectorMap.put(selName, c);
					return c;
				}
			}
		}

		throw new AssertionError("No constructor for selector " + selector);
	}
}
