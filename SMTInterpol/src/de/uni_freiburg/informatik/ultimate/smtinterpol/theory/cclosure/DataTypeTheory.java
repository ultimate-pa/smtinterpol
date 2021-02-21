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

public class DataTypeTheory implements ITheory {
	
	private final Clausifier mClausifier;
	private final CClosure mCClosure;
	private final Theory mTheory;
	private final ArrayDeque<SymmetricPair<CCTerm>>mPendingEqualities = new ArrayDeque<SymmetricPair<CCTerm>>();
	private final LinkedHashMap<String, Constructor> mSelectorMap = new LinkedHashMap<>();
	private final ArrayDeque<Clause> mConflicts = new ArrayDeque<>();
	private ArrayQueue<CCTerm> mRecheckOnBacktrack = new ArrayQueue<>();
	private final LinkedHashMap<Sort, Boolean> mInfinityMap = new LinkedHashMap<>();
	private final LinkedHashMap<SymmetricPair<CCTerm>, ArrayList<SymmetricPair<CCTerm>>> mEqualityReasons = new LinkedHashMap<>();
	
	public DataTypeTheory(Clausifier clausifier, Theory theory, CClosure cclosure) {
		mClausifier = clausifier;
		mCClosure = cclosure;
		mTheory = theory;
	}
	
	public void addPendingEquality(SymmetricPair<CCTerm> eq, ArrayList<SymmetricPair<CCTerm>> reason) {
		if (eq.getFirst() == eq.getSecond() || eq.getFirst().mRepStar == eq.getSecond().mRepStar) {
			return;
		}
		mPendingEqualities.add(eq);
		mEqualityReasons.put(eq, reason);
		
//		if (mEqualityReasons.containsKey(eq)) {
//			// check if exisiting reason still holds
//			for (SymmetricPair<CCTerm> pair : mEqualityReasons.get(eq)) {
//				if (pair.getFirst().mRepStar != pair.getSecond().mRepStar) {
//					mEqualityReasons.put(eq, reason);
//					return;
//				}
//			}
//		} else {
//			mEqualityReasons.put(eq, reason);
//		}
	}
	
	public void addConflict(Clause clause) {
		mConflicts.add(clause);
	}

	@Override
	public Clause startCheck() {
		return null;
	}

	@Override
	public void endCheck() {
		// TODO Auto-generated method stub

	}

	@Override
	public Clause setLiteral(Literal literal) {		
		return null;
	}

	@Override
	public void backtrackLiteral(Literal literal) {
		// TODO Auto-generated method stubfinal

	}

	@Override
	public Clause checkpoint() {
		if (!mConflicts.isEmpty()) {
			return mConflicts.poll();
		}
		
		// Rule 3:
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
						// Rule 9: if this is-Function tests for a another constructor than the is-Functions
						// we already saw for this congruence class, there is a conflict.
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
								return new Clause(negLits);
							}
						}
					}
				}
			}
		}
		
		LinkedHashSet<CCTerm> DTReps = new LinkedHashSet<>();
		for (CCTerm ct : mCClosure.mAllTerms) {
			if (ct == ct.mRep && ct.mFlatTerm != null && ct.mFlatTerm.getSort().getSortSymbol().isDatatype()) DTReps.add(ct);
		}
		
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
				if (isIndices.size() == dt.getConstructors().length) {
					HashSet<Literal> lits = new HashSet<>();
					for (CCTerm isFun : isIndices.values()) {
						CongruencePath cp = new CongruencePath(mCClosure);
						cp.computePath(isFun, falseRep);
						lits.addAll(cp.mAllLiterals);
					}
					Literal[] negLits = new Literal[lits.size()];
					int i = 0;
					for (Literal l : lits) {
						negLits[i++] = l.negate();
					}
					return new Clause(negLits);
				}
			}
		}
		
		for (CCTerm ct : DTReps) {
			Rule4(ct);
			Rule5(ct);
			
			Clause cl = Rule8(ct);
			if (cl != null) return cl;
		}
		
		
		return null;
	}

	@Override
	public Clause computeConflictClause() {
		// check for cycles (Rule7)
		LinkedHashSet<CCTerm> visited = new LinkedHashSet<>();
		
		// DFS Cycle Detection
		Deque<CCTerm> path = new ArrayDeque<>();
		Set<CCTerm> visitedOnPath = new LinkedHashSet<>();
		Deque<CCTerm> todo = new ArrayDeque<>();
		Map<CCTerm, SymmetricPair<CCTerm>> argConsPairs = new LinkedHashMap<>();
		Set<CCTerm> possibleCons = new LinkedHashSet<>();
		
		for (CCTerm start : mCClosure.mAllTerms) {
			if (start == start.mRepStar && start.mFlatTerm != null && start.mFlatTerm.getSort().getSortSymbol().isDatatype()) {
				todo.push(start);
				
				while (!todo.isEmpty()) {
					final CCTerm ct = todo.pop();
					final CCTerm rep = ct.mRepStar;
					if (visited.contains(rep)) {
						if (path.peek() == rep) {
							path.pop();
							visitedOnPath.remove(rep);
						} else if (visitedOnPath.contains(rep)) {
							// build and return conflict clause
							Set<Literal> literals = new HashSet<>();
							CCTerm lastCt = ct;
							while (!path.isEmpty()) {
								CCTerm pathRep = path.pop();
								SymmetricPair<CCTerm> pair = argConsPairs.get(pathRep);
								
								// if it is not sure that pathRep is the matching constructor to the selector (lastCT)
								// build an is-function
								if (possibleCons.contains(pathRep)) {
									String selName = ((ApplicationTerm) lastCt.mFlatTerm).getFunction().getName();
									Sort repSort = pathRep.mFlatTerm.getSort();
									for (Constructor c : ((DataType) repSort.getSortSymbol()).getConstructors()) {
										for (String s : c.getSelectors()) {
											if (s.equals(selName)) {
												Term isTerm = mTheory.term(mTheory.getFunctionWithResult("is", new String[] {c.getName()}, null, repSort), pair.getFirst().mFlatTerm);
												CCTerm isCCTerm = mClausifier.createCCTerm(isTerm, SourceAnnotation.EMPTY_SOURCE_ANNOT);
												return null;
											}
										}
									}
									mClausifier.getLogger().error("Should have found the matching constructor to %s", selName);
									return null;
								}								
								
								CongruencePath cp = new CongruencePath(mCClosure);

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
						CCTerm trueRep = mClausifier.getCCTerm(mTheory.mTrue).mRepStar;
//						CCTerm falseRep = mClausifier.getCCTerm(mTheory.mFalse).mRepStar;
						Set<CCTerm> selectors = new LinkedHashSet<>();
						Set<String> rightSelectors = new LinkedHashSet<>();
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
						
						for (CCTerm s : selectors) {
							String fsName = ((ApplicationTerm)s.mFlatTerm).getFunction().getName();
							if ((!rightSelectors.isEmpty() && rightSelectors.contains(fsName)) || !falseSelectors.contains(fsName)) {
								todo.push(s);
								if (!rightSelectors.contains(fsName)) possibleCons.add(rep);
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
			//return mCClosure.createCCEquality(mClausifier.getStackLevel(), eqPair.getFirst(), eqPair.getSecond());
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
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public int checkCompleteness() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public void printStatistics(LogProxy logger) {
		// TODO Auto-generated method stub

	}

	@Override
	public void dumpModel(LogProxy logger) {
		// TODO Auto-generated method stub

	}

	@Override
	public void increasedDecideLevel(int currentDecideLevel) {
		// TODO Auto-generated method stub

	}

	@Override
	public void decreasedDecideLevel(int currentDecideLevel) {
		// TODO Auto-generated method stub

	}

	@Override
	public Clause backtrackComplete() {
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
		// TODO Auto-generated method stub

	}

	@Override
	public void restart(int iteration) {
		// TODO Auto-generated method stub

	}

	@Override
	public void removeAtom(DPLLAtom atom) {
		// TODO Auto-generated method stub

	}

	@Override
	public void push() {
		// TODO Auto-generated method stub

	}

	@Override
	public void pop() {
		mInfinityMap.clear();
	}

	@Override
	public Object[] getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}
	
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
		
		// construct a new constructor application like C(s1(x), s2(x), ..., sm(x))
		
		Term consTerm = mTheory.term(consName, (Term[]) selectorApps.values().toArray(new Term[selectorApps.values().size()]));
		CCTerm consCCTerm = mClausifier.createCCTerm(consTerm, SourceAnnotation.EMPTY_SOURCE_ANNOT);
		SymmetricPair<CCTerm> eq = new SymmetricPair<CCTerm>(argRep, consCCTerm);
		ArrayList<SymmetricPair<CCTerm>> reason = new ArrayList<>();
		if (arg != argRep.mFlatTerm) reason.add(new SymmetricPair<CCTerm>(mClausifier.getCCTerm(arg), argRep));
		reason.add(new SymmetricPair<CCTerm>(isTerm, mClausifier.getCCTerm(mTheory.mTrue)));
		addPendingEquality(eq, reason);
		
	}
	
	private void Rule4(CCTerm ccterm) {
		LinkedHashSet<String> exisitingSelectors = findAllSelectorApplications(ccterm);
		
		SortSymbol sym = ccterm.mFlatTerm.getSort().getSortSymbol();
		for (Constructor c : ((DataType) sym).getConstructors()) {
			// check if only selectors with finite return sort are missing and build them
			boolean noInfSel = true;
			LinkedHashSet<String> neededSelectors = new LinkedHashSet<>();
			for (int i = 0; i < c.getSelectors().length; i++) {
				if (!exisitingSelectors.contains(c.getSelectors()[i])) {
					if (!c.getArgumentSorts()[i].getSortSymbol().isDatatype() || isInfinite(c.getArgumentSorts()[i], new LinkedHashSet<>())) {
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
//							mUnitClauseReasons.put(eqPair, new SymmetricPair<CCTerm>(mem, consCCTerm));
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
	
	private LinkedHashSet<String> findAllSelectorApplications(CCTerm ccterm) {
		LinkedHashSet<String> selApps = new LinkedHashSet<>();
		CCParentInfo parInfo = ccterm.mRepStar.mCCPars;
		while (parInfo != null) {
			if (parInfo.mCCParents != null && !parInfo.mCCParents.isEmpty()) {
					//FunctionSymbol fun = ((ApplicationTerm) parInfo.mCCParents.getElem().getData().getFlatTerm()).getFunction();
					Parent p = parInfo.mCCParents.iterator().next();
					ApplicationTerm pAt = (ApplicationTerm) p.getData().getFlatTerm();
					if (pAt != null && pAt.getFunction().isSelector()) selApps.add(pAt.getFunction().getName());
			}
			parInfo = parInfo.mNext;
		}
		return selApps;
	}
	
	private boolean isInfinite(Sort sort, LinkedHashSet<Sort> dependents) {
		dependents.add(sort);
		Boolean cacheVal = mInfinityMap.get(sort);
		if (cacheVal != null) return cacheVal;
		if (sort.getSortSymbol().isDatatype()) {
			for (Constructor c : ((DataType) sort.getSortSymbol()).getConstructors()) {
				for (Sort as : c.getArgumentSorts()) {
					// if a constructor of the sort of this argument has a argument with Sort "sort" the sort is infinite
					if (dependents.contains(as)) {
						mInfinityMap.put(sort, true);
						return true;
					}
					if (isInfinite(as, dependents)) {
						mInfinityMap.put(sort, true);
						return true;
					}
				}
			}
			mInfinityMap.put(sort, false);
			return false;
		} else if (sort.isNumericSort()) {
			mInfinityMap.put(sort, true);
			return true;
		}
		mInfinityMap.put(sort, false);
		return false;
	}

}
