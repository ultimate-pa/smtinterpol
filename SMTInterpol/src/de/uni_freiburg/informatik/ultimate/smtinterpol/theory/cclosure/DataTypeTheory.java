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
	private final ArrayDeque<SymmetricPair<CCTerm>>mPendingEqualities = new ArrayDeque<SymmetricPair<CCTerm>>();
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
	private final LinkedHashMap<SymmetricPair<CCTerm>, ArrayList<SymmetricPair<CCTerm>>> mEqualityReasons = new LinkedHashMap<>();
	
	public DataTypeTheory(Clausifier clausifier, Theory theory, CClosure cclosure) {
		mClausifier = clausifier;
		mCClosure = cclosure;
		mTheory = theory;
	}
	
	/**
	 * add a new equality between two terms to be propagated.
	 * @param eq the terms that are equal.
	 * @param reason the terms which are needed for the unit clause generation.
	 */
	public void addPendingEquality(SymmetricPair<CCTerm> eq, ArrayList<SymmetricPair<CCTerm>> reason) {
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
	public Clause setLiteral(Literal literal) {		
		return null;
	}

	@Override
	public void backtrackLiteral(Literal literal) {
	}

	@Override
	public Clause checkpoint() {
		
		//Visit all ((_ is CONS) u) terms that are true and try to apply rule 3 or 9 on them
		CCTerm trueRep = mCClosure.getCCTermRep(mTheory.mTrue);
		LinkedHashMap<CCTerm, LinkedHashSet<CCAppTerm>> visited = new LinkedHashMap<>();
		for (CCTerm t : trueRep.mMembers) {
			if (t instanceof CCAppTerm && t.mFlatTerm instanceof ApplicationTerm) {
				ApplicationTerm at = (ApplicationTerm) t.mFlatTerm;
				CCAppTerm ccat = (CCAppTerm) t;
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
						for (CCAppTerm visitor : visited.get(ccat.mArg.mRepStar)) {
							if (visitor.getFunc().mParentPosition != ccat.getFunc().mParentPosition) {
								CongruencePath cpIs = new CongruencePath(mCClosure);
								CongruencePath cpArg = new CongruencePath(mCClosure);
								cpIs.computePath(visitor, ccat);
								cpArg.computePath(ccat.mArg, visitor.mArg);
								HashSet<Literal> lits = new HashSet<>();
								lits.addAll(cpIs.mAllLiterals);
								lits.addAll(cpArg.mAllLiterals);
								Literal[] negLits = new Literal[lits.size()];
								int i = 0;
								for (Literal l : lits) {
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
		LinkedHashMap<CCTerm, LinkedHashSet<CCTerm>> falseIsFuns = new LinkedHashMap<>();
		CCTerm falseRep = mCClosure.getCCTermRep(mTheory.mFalse);
		for (CCTerm cct : falseRep.mMembers) {
			if (cct.mFlatTerm instanceof ApplicationTerm && ((ApplicationTerm) cct.mFlatTerm).getFunction().getName().equals("is")) {
				falseIsFuns.putIfAbsent(((CCAppTerm)cct).mArg.mRepStar, new LinkedHashSet<>());
				falseIsFuns.get(((CCAppTerm)cct).mArg.mRepStar).add(cct);
			}
		}
		
		for (CCTerm cct : falseIsFuns.keySet()) {
			DataType dt = (DataType) cct.mFlatTerm.getSort().getSortSymbol();
			if (falseIsFuns.get(cct).size() >= dt.getConstructors().length) {
				LinkedHashMap<String, CCTerm> isIndices = new LinkedHashMap<>();
				for (CCTerm isFun : falseIsFuns.get(cct)) {
					isIndices.put(((ApplicationTerm) isFun.mFlatTerm).getFunction().getIndices()[0], isFun);
				}
				/*
				 * Rule 6:
				 * Every data type term must be equal to a constructor.
				 * Thus, not all "is" functions may be false.
				 */
				if (isIndices.size() == dt.getConstructors().length) {
					HashSet<Literal> lits = new HashSet<>();
					for (CCTerm isFun : isIndices.values()) {
						CongruencePath cp = new CongruencePath(mCClosure);
						cp.computePath(isFun, falseRep);
						cp.computePath(((CCAppTerm)isFun).mArg, cct);
						lits.addAll(cp.mAllLiterals);
					}
					Literal[] negLits = new Literal[lits.size()];
					int i = 0;
					for (Literal l : lits) {
						negLits[i++] = l.negate();
					}
					mClausifier.getLogger().debug("Conflict: Rule 6");
					return new Clause(negLits);
				}
			}
		}
		
		LinkedHashSet<CCTerm> DTReps = new LinkedHashSet<>();
		for (CCTerm ct : mCClosure.mAllTerms) {
			if (ct == ct.mRep && ct.mFlatTerm != null && ct.mFlatTerm.getSort().getSortSymbol().isDatatype()) DTReps.add(ct);
		}
		
		for (CCTerm ct : DTReps) {
			Rule4(ct);
			Rule5(ct);
			
			Clause cl = Rule8(ct);
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
		LinkedHashSet<CCTerm> visited = new LinkedHashSet<>();
		
		
		Deque<CCTerm> path = new ArrayDeque<>();
		Set<CCTerm> visitedOnPath = new LinkedHashSet<>();
		Deque<CCTerm> todo = new ArrayDeque<>();
		Map<CCTerm, SymmetricPair<CCTerm>> argConsPairs = new LinkedHashMap<>();
		Map<CCTerm, CCAppTerm> possibleCons = new LinkedHashMap<>();
		
		for (CCTerm start : mCClosure.mAllTerms) {
			if (start == start.mRepStar && start.mFlatTerm != null && start.mFlatTerm.getSort().getSortSymbol().isDatatype()) {
				todo.push(start);
				
				while (!todo.isEmpty()) {
					final CCTerm ct = todo.pop();
					final CCTerm rep = ct.mRepStar;
					if (visited.contains(rep)) {
						if (path.peek() == rep) {
							// if the current term is the last on the path, we didn't find a cycle and we are backtracking.
							path.pop();
							visitedOnPath.remove(rep);
						} else if (visitedOnPath.contains(rep)) {
							// if we already visited rep on our current path, it is a cycle.
							// build and return conflict clause
							Set<Literal> literals = new HashSet<>();
							CCTerm lastCt = ct;
							while (!path.isEmpty()) {
								CCTerm pathRep = path.pop();
								SymmetricPair<CCTerm> pair = argConsPairs.get(pathRep);
								CongruencePath cp = new CongruencePath(mCClosure);
								
								// if it is not sure that pathRep is the matching constructor to the selector (lastCT)
								// build an is-function
								if (possibleCons.containsKey(pathRep)) {
									CCAppTerm isFun = possibleCons.get(pathRep);
									if (isFun == null) {
										String selName = ((ApplicationTerm) lastCt.mFlatTerm).getFunction().getName();
										Sort repSort = pathRep.mFlatTerm.getSort();
										for (Constructor c : ((DataType) repSort.getSortSymbol()).getConstructors()) {
											for (String s : c.getSelectors()) {
												if (s.equals(selName)) {
													Term isTerm = mTheory.term(mTheory.getFunctionWithResult("is", new String[] {c.getName()}, null, repSort), pair.getFirst().mFlatTerm);
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
									pair = new SymmetricPair<CCTerm>(pair.getFirst(), ((CCAppTerm)lastCt).mArg);
								}
								
								if (rep == pathRep) {
									cp.computePath(ct, pair.getSecond());
									literals.addAll(cp.mAllLiterals);
									break;
								}
								cp.computePath(pair.getFirst(), pair.getSecond());
								literals.addAll(cp.mAllLiterals);
								lastCt = pair.getFirst();
							}
							Literal[] negLits = new Literal[literals.size()];
							int i = 0;
							for (Literal l : literals) {
								negLits[i++] = l.negate();
							}
							mClausifier.getLogger().debug("Found Cycle: %s", literals);
							return new Clause(negLits);
						}
						continue;
					}
					
					boolean foundConstructor = false;
					// if this eq class contains a constructor add all data type arguments to the todo stack
					for (CCTerm mem : rep.mMembers) {
						if (mem.mFlatTerm instanceof ApplicationTerm && ((ApplicationTerm)mem.mFlatTerm).getFunction().isConstructor()) {
							foundConstructor = true;
							path.push(rep);
							visitedOnPath.add(rep);
							todo.push(ct);
							argConsPairs.put(rep, new SymmetricPair<CCTerm>(ct, mem));
							for (Term arg : ((ApplicationTerm)mem.mFlatTerm).getParameters()) {
								if (arg.getSort().getSortSymbol().isDatatype()) {
									CCTerm ccArg = mClausifier.getCCTerm(arg);
									if (ccArg.mRepStar == rep) {
										// if an argument of a constructor is equal to the constructor itself
										// we need to build the conflict clause directly, otherwise we would assume
										// we were backtracking.
										CongruencePath cp = new CongruencePath(mCClosure);
										cp.computePath(ccArg, mem);
										Literal[] negLits = new Literal[cp.mAllLiterals.size()];
										int i = 0;
										for (Literal l : cp.mAllLiterals) {
											negLits[i++] = l.negate();
										}
										return new Clause(negLits);
									}
									todo.push(mClausifier.getCCTerm(arg));
								}
							}
							break;
						}
					}

					if (!foundConstructor) {
						// if there is no constructor in this equality class,
						// we need to search for a selector function application.
						CCTerm trueRep = mClausifier.getCCTerm(mTheory.mTrue).mRepStar;
						Set<CCAppTerm> selectors = new LinkedHashSet<>();
						Set<String> rightSelectors = new LinkedHashSet<>();
						CCAppTerm trueIsFunction = null;
						Set<String> falseSelectors = new LinkedHashSet<>();
						CCParentInfo pInfo = rep.mCCPars;
						while (pInfo != null) {
							if (pInfo.mCCParents != null && pInfo.mCCParents.iterator().hasNext()) {
								CCAppTerm p = pInfo.mCCParents.iterator().next().getData();
								if (p.mFlatTerm instanceof ApplicationTerm) {
									FunctionSymbol pFun = ((ApplicationTerm) p.mFlatTerm).getFunction();
									if (pFun.isSelector() && p.mFlatTerm.getSort().getSortSymbol().isDatatype()) {
										selectors.add(p);
									} else if (pFun.getName().equals("is")) {
										Constructor c = ((DataType)rep.mFlatTerm.getSort().getSortSymbol()).findConstructor(pFun.getIndices()[0]);
										if (p.mRepStar == trueRep) {
											rightSelectors.addAll(Arrays.asList(c.getSelectors()));
											trueIsFunction = p;
										} else {
											falseSelectors.addAll(Arrays.asList(c.getSelectors()));
										}
									}
								}
							}
							pInfo = pInfo.mNext;
						}
						
						if (!selectors.isEmpty()) {
							path.push(rep);
							visitedOnPath.add(rep);
							todo.push(ct);
							argConsPairs.put(rep, new SymmetricPair<CCTerm>(ct, null));
						}
						
						for (CCAppTerm s : selectors) {
							String fsName = ((ApplicationTerm)s.mFlatTerm).getFunction().getName();
							if ((!rightSelectors.isEmpty() && rightSelectors.contains(fsName)) || !falseSelectors.contains(fsName)) {
								if (s.mRepStar == rep) {
									// if the selector is in the same class as its argument it is a cycle
									// but only if the argument is the right constructor
									if (trueIsFunction == null) {
										Constructor cons = getConstructor((ApplicationTerm) s.mFlatTerm);
										Term isTerm = mTheory.term(mTheory.getFunctionWithResult("is", new String[] {cons.getName()}, null, rep.mFlatTerm.getSort()), s.mArg.mFlatTerm);
										mClausifier.createCCTerm(isTerm, SourceAnnotation.EMPTY_SOURCE_ANNOT);
										return null;
									} else {
										CongruencePath cp = new CongruencePath(mCClosure);
										cp.computePath(mClausifier.getCCTerm(mTheory.mTrue), trueIsFunction);
										cp.computePath(trueIsFunction.mArg, s.mArg);
										cp.computePath(s, s.mArg);
										int i = 0;
										Literal[] negLits = new Literal[cp.mAllLiterals.size()];
										for (Literal l : cp.mAllLiterals) {
											negLits[i++] = l.negate();
										}
										return new Clause(negLits);
									}
								}
								
								todo.push(s);
								possibleCons.put(rep, trueIsFunction);
							}
						}
					}
					visited.add(rep);
				}
			}
		}
		return null;
	}

	@Override
	public Literal getPropagatedLiteral() {
		if (!mPendingEqualities.isEmpty()) {
			SymmetricPair<CCTerm> eqPair = mPendingEqualities.poll();
			return mCClosure.createEquality(eqPair.getFirst(), eqPair.getSecond(), false);
		}
		return null;
	}

	@Override
	public Clause getUnitClause(Literal literal) {
		CCEquality eq = (CCEquality) literal;
		
		ArrayList<SymmetricPair<CCTerm>> reason = mEqualityReasons.get(new SymmetricPair<CCTerm>(eq.getLhs(), eq.getRhs()));
		if (reason == null) return null;
		HashSet<Literal> lits = new HashSet<>();
		for (SymmetricPair<CCTerm> pair : reason) {
			CongruencePath cp = new CongruencePath(mCClosure);
			cp.computePath(pair.getFirst(), pair.getSecond());
			lits.addAll(cp.mAllLiterals);
		}
		
		Literal[] negLits = new Literal[lits.size() + 1];
		int i = 0;
		negLits [i++] = literal;
		for (Literal l : lits) {
			negLits[i++] = l.negate();
		}
		
		return new Clause(negLits);
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
	public void printStatistics(LogProxy logger) {
	}

	@Override
	public void dumpModel(LogProxy logger) {
	}

	@Override
	public void increasedDecideLevel(int currentDecideLevel) {
	}

	@Override
	public void decreasedDecideLevel(int currentDecideLevel) {
	}

	@Override
	public Clause backtrackComplete() {
		// if we constructed new terms, their equalities have been removed in the backtracking process,
		// so we need to check if they are still valid.
		mPendingEqualities.clear();
		ArrayQueue<CCTerm> newRecheckOnBacktrack = new ArrayQueue<>();
		while (!mRecheckOnBacktrack.isEmpty()) {
			ApplicationTerm constructor = null;
			CCTerm checkTerm = mRecheckOnBacktrack.poll();
			for (CCTerm ct : ((CCAppTerm) checkTerm).mArg.mRepStar.mMembers) {
				if (ct.mFlatTerm instanceof ApplicationTerm && ((ApplicationTerm) ct.mFlatTerm).getFunction().isConstructor()) {
					constructor = (ApplicationTerm) ct.mFlatTerm;
					break;
				}
			}
			if (constructor == null) continue;
			ArrayList<SymmetricPair<CCTerm>> reason = new ArrayList<>();
			reason.add(new SymmetricPair<CCTerm>(((CCAppTerm) checkTerm).getArg(), mClausifier.getCCTerm(constructor)));
			if (((ApplicationTerm) checkTerm.mFlatTerm).getFunction().isSelector()) {
				String selName = ((ApplicationTerm) checkTerm.mFlatTerm).getFunction().getName();
				Constructor c = mSelectorMap.get(selName);
				assert c.getName().equals(constructor.getFunction().getName());
				for (int i = 0; i < c.getSelectors().length; i++) {
					if (selName.equals(c.getSelectors()[i])) {
						CCTerm arg = mClausifier.getCCTerm(constructor.getParameters()[i]);
						if (arg.mRepStar != checkTerm.mRepStar) addPendingEquality(new SymmetricPair<CCTerm>(arg, checkTerm), reason);
						newRecheckOnBacktrack.add(checkTerm);
					}
				}
			} else {
				if (constructor.getFunction().getName().equals(((ApplicationTerm) checkTerm.mFlatTerm).getFunction().getIndices()[0])) {
					CCTerm ccTrue = mClausifier.getCCTerm(mTheory.mTrue);
					if (ccTrue.mRepStar != checkTerm.mRepStar) addPendingEquality(new SymmetricPair<CCTerm>(checkTerm, mClausifier.getCCTerm(mTheory.mTrue)), reason);
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
	public void restart(int iteration) {
	}

	@Override
	public void removeAtom(DPLLAtom atom) {
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
		return null;
	}
	
	// TODO: rename
	/**
	 * Rule 3 checks if the argument of the isTerm has an application for every 
	 * selector function and if so, builds a constructor term based on these selector functions.
	 * @param isTerm a "is" function term equal to true.
	 */
	private void Rule3(CCAppTerm isTerm) {
		// check if there is already a constructor application equal to the argument
		ApplicationTerm at = (ApplicationTerm) isTerm.mFlatTerm;
		Term arg = at.getParameters()[0];
		
		//CCTerm argRep = mCClosure.getCCTermRep(arg);
		CCTerm argRep = isTerm.mArg.mRepStar;
		String consName = at.getFunction().getIndices()[0];
		if (argRep == null) {
			return;
		}
		for (CCTerm mt : argRep.mMembers) {
			if (mt.mFlatTerm instanceof ApplicationTerm) {
				ApplicationTerm mat = (ApplicationTerm) mt.mFlatTerm;
				String matName = mat.getFunction().getName();
				if (matName.equals(consName)) {
					return;
				}
			}
		}

		// check if there are all selector applications on the eq class
		DataType dt = (DataType) at.getFunction().getParameterSorts()[0].getSortSymbol();
		Constructor c = dt.findConstructor(consName);
		
		LinkedHashMap<String, Term> selectorApps = new LinkedHashMap<>();
		for (String s : c.getSelectors()) selectorApps.put(s, null);
		
		if (selectorApps.size() > 0) {
			CCParentInfo argParInfo = argRep.mCCPars;
			while (argParInfo != null) {
				if (argParInfo.mCCParents != null) {
					for (Parent p : argParInfo.mCCParents) {
						if (p.getData().mFlatTerm instanceof ApplicationTerm) {
							String parFunName = ((ApplicationTerm) p.getData().mFlatTerm).getFunction().getName();
							if (selectorApps.containsKey(parFunName)) {
								selectorApps.put(parFunName, mTheory.term(parFunName, new Term[] {arg}));
							}
						}
					}
				}
				argParInfo = argParInfo.mNext;
			}
		}
		
		if (selectorApps.containsValue(null)) return;
		
		// create a new constructor application like C(s1(x), s2(x), ..., sm(x))
		
		Term consTerm = mTheory.term(consName, (Term[]) selectorApps.values().toArray(new Term[selectorApps.values().size()]));
		CCTerm consCCTerm = mClausifier.createCCTerm(consTerm, SourceAnnotation.EMPTY_SOURCE_ANNOT);
		SymmetricPair<CCTerm> eq = new SymmetricPair<CCTerm>(argRep, consCCTerm);
		ArrayList<SymmetricPair<CCTerm>> reason = new ArrayList<>();
		if (arg != argRep.mFlatTerm) reason.add(new SymmetricPair<CCTerm>(mClausifier.getCCTerm(arg), argRep));
		reason.add(new SymmetricPair<CCTerm>(isTerm, mClausifier.getCCTerm(mTheory.mTrue)));
		addPendingEquality(eq, reason);
		
	}

	/**
	 * Rule 4 checks for a term if all missing selector function applications are of a finite sort
	 * and if so, builds them.
	 * 
	 * @param ccterm a term with DataType sort.
	 */
	private void Rule4(CCTerm ccterm) {
		LinkedHashSet<String> exisitingSelectors = findAllSelectorApplications(ccterm);
		
		SortSymbol sym = ccterm.mFlatTerm.getSort().getSortSymbol();
		for (Constructor c : ((DataType) sym).getConstructors()) {
			// check if only selectors with finite return sort are missing and build them
			boolean noInfSel = true;
			LinkedHashSet<String> neededSelectors = new LinkedHashSet<>();
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
				for (String sel : neededSelectors) {
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
	private void Rule5(CCTerm ccterm) {
		LinkedHashSet<String> selApps = findAllSelectorApplications(ccterm);
		SortSymbol sym = ccterm.mFlatTerm.getSort().getSortSymbol();
		
		// check if there is already a constructor
		for (CCTerm mem : ccterm.mMembers) {
			if (mem.mFlatTerm instanceof ApplicationTerm && ((ApplicationTerm)mem.mFlatTerm).getFunction().isConstructor()) return;
		}
		
		for (Constructor c : ((DataType) sym).getConstructors()) {
			if (selApps.containsAll(Arrays.asList(c.getSelectors()))) {
				FunctionSymbol isFs = mTheory.getFunctionWithResult("is", new String[] {c.getName()}, null, new Sort[] {ccterm.getFlatTerm().getSort()});
				Term isTerm = mTheory.term(isFs, ccterm.mFlatTerm);
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
	private Clause Rule8(CCTerm ccterm) {
		ApplicationTerm consAt = null;
		CCTerm consCCTerm = null;
		for (CCTerm mem : ccterm.mMembers) {
			if (mem.mFlatTerm instanceof ApplicationTerm && ((ApplicationTerm) mem.mFlatTerm).getFunction().isConstructor()) {
				ApplicationTerm memAt = (ApplicationTerm) mem.getFlatTerm();
				if (consAt == null) {
					consAt = memAt;
					consCCTerm = mClausifier.getCCTerm(consAt);
					continue;
				}
				if (memAt.getFunction() == consAt.getFunction()) {
					for (int i = 0; i < memAt.getParameters().length; i++) {
						CCTerm memArg = mClausifier.getCCTerm(memAt.getParameters()[i]);
						CCTerm consArg = mClausifier.getCCTerm(consAt.getParameters()[i]);
						if (memArg.mRepStar != consArg.mRepStar) {
							SymmetricPair<CCTerm> eqPair = new SymmetricPair<CCTerm>(memArg, consArg);
							ArrayList<SymmetricPair<CCTerm>> reason = new ArrayList<>();
							reason.add(new SymmetricPair<CCTerm>(consCCTerm, mem));
							addPendingEquality(eqPair, reason);
						}
					}
				} else {
					CongruencePath cp = new CongruencePath(mCClosure);
					cp.computePath(mem, consCCTerm);
					Literal[] lits = new Literal[cp.mAllLiterals.size()];
					int i = 0;
					for (Literal l : cp.mAllLiterals) {
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
	private LinkedHashSet<String> findAllSelectorApplications(CCTerm ccterm) {
		LinkedHashSet<String> selApps = new LinkedHashSet<>();
		CCParentInfo parInfo = ccterm.mRepStar.mCCPars;
		while (parInfo != null) {
			if (parInfo.mCCParents != null && !parInfo.mCCParents.isEmpty()) {
					Parent p = parInfo.mCCParents.iterator().next();
					ApplicationTerm pAt = (ApplicationTerm) p.getData().getFlatTerm();
					if (pAt != null && pAt.getFunction().isSelector()) selApps.add(pAt.getFunction().getName());
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
	private boolean isInfinite(Sort sort) {
		Boolean cacheVal = mInfinityMap.get(sort);
		if (cacheVal != null) return cacheVal;
		ArrayDeque<Sort> todo = new ArrayDeque<>();
		Set<Sort> dependent = new LinkedHashSet<>();
		todo.push(sort);
		todo_loop: while (!todo.isEmpty()) {
			Sort currSort = todo.pop();
			Set<Sort> undecided = new LinkedHashSet<>();
			if (currSort.getSortSymbol().isDatatype()) {
				for (Constructor c : ((DataType)currSort.getSortSymbol()).getConstructors()) {
					for (Sort argSort : c.getArgumentSorts()) {
						Boolean cv = mInfinityMap.get(argSort);
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
					for (Sort s: undecided) todo.push(s);
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
	private Constructor getConstructor(ApplicationTerm selector) {
		if (!selector.getFunction().isSelector()) return null;
		
		String selName = selector.getFunction().getName();
		if (mSelectorMap.containsKey(selector.getFunction().getName())) return mSelectorMap.get(selector.getFunction().getName());
		
		for (Constructor c : ((DataType)selector.getParameters()[0].getSort().getSortSymbol()).getConstructors()) {
			for (String s : c.getSelectors()) {
				if (s.equals(selName)) {
					mSelectorMap.put(selName, c);
					return c;
				}
			}
		}
		
		return null;
	}

}
