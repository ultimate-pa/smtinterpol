package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;

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
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

public class DataTypeTheory implements ITheory {
	
	private final Clausifier mClausifier;
	private final CClosure mCClosure;
	private final Theory mTheory;
	private final ArrayDeque<SymmetricPair<CCTerm>> mPendingEqualities;
	private final LinkedHashMap<String, Constructor> mSelectorMap;
	private final LinkedHashMap<SortSymbol, Boolean> mInfinitSortsMap;
	private final ArrayDeque<Clause> mConflicts;
	
	public DataTypeTheory(Clausifier clausifier, Theory theory, CClosure cclosure) {
		mClausifier = clausifier;
		mCClosure = cclosure;
		mTheory = theory;
		mPendingEqualities = new ArrayDeque<SymmetricPair<CCTerm>>();
		mSelectorMap = new LinkedHashMap<>();
		mInfinitSortsMap = new LinkedHashMap<>();
		mConflicts = new ArrayDeque<>();
	}
	
	public void addPendingEquality(SymmetricPair<CCTerm> pair) {
		mPendingEqualities.add(pair);
	}
	
	public void addConflict(Clause clause) {
		mConflicts.add(clause);
	}

	@Override
	public Clause startCheck() {
		LinkedHashMap<SortSymbol, ArrayDeque<SortSymbol>> deps = new LinkedHashMap<>();
		ArrayDeque<SortSymbol> undecidedSorts = new ArrayDeque<>();
		for (SortSymbol sym : mTheory.getDeclaredSorts().values()) {
			if (sym.isDatatype()) {
				ArrayDeque<SortSymbol> dependsOn = new ArrayDeque<>();
				for (Constructor cons : ((DataType) sym).getConstructors()) {
					for (String sel : cons.getSelectors()) {
						mSelectorMap.put(sel, cons);
					}
					for (Sort argSort : cons.getArgumentSorts()) {
						// TODO: are arraysSorts also infinite?
						if (argSort.getSortSymbol() == sym || mInfinitSortsMap.containsKey(argSort.getSortSymbol()) || argSort.isNumericSort()) {
							mInfinitSortsMap.put(sym, true);
						} else {
							dependsOn.add(argSort.getSortSymbol());
						}
					}
				}
				if (!mInfinitSortsMap.containsKey(sym)) {
					if (dependsOn.isEmpty()) {
						mInfinitSortsMap.put(sym, false);
					} else {
						deps.put(sym, dependsOn);
						undecidedSorts.add(sym);
					}
				}
			}
		}
		
		int noDecisionCounter = 0;
		while (!undecidedSorts.isEmpty() && noDecisionCounter < undecidedSorts.size()) {
			noDecisionCounter++;
			SortSymbol sym = undecidedSorts.poll();
			ArrayDeque<SortSymbol> dependsOn = new ArrayDeque<>();
			while (!deps.get(sym).isEmpty()) {
				SortSymbol dSym = deps.get(sym).poll();
				if (mInfinitSortsMap.containsKey(dSym)) {
					if (mInfinitSortsMap.get(dSym)) {
						mInfinitSortsMap.put(sym, true);
						noDecisionCounter = 0;
					}
				} else {
					dependsOn.add(dSym);
				}
			}
			if (!mInfinitSortsMap.containsKey(sym)) {
				if (dependsOn.isEmpty()) {
					mInfinitSortsMap.put(sym, false);
					noDecisionCounter = 0;
				} else {
					deps.put(sym, dependsOn);
					undecidedSorts.add(sym);
				}
			}
		}
		// if undecidedSorts is not empty there are sorts which depend on each other and are therefore infinite
		for (SortSymbol sym : undecidedSorts) {
			mInfinitSortsMap.put(sym, true);
		}
		
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
		// TODO Auto-generated method stub

	}

	@Override
	public Clause checkpoint() {
		if (!mConflicts.isEmpty()) {
			return mConflicts.poll();
		}
		
		// Rule 3:
		CCTerm trueRep = mCClosure.getCCTermRep(mClausifier.getTheory().mTrue);
		LinkedHashSet<CCTerm> visited = new LinkedHashSet<>();
		for (CCTerm t : trueRep.mMembers) {
			if (t instanceof CCAppTerm && t.mFlatTerm instanceof ApplicationTerm) {
				ApplicationTerm at = (ApplicationTerm) t.mFlatTerm;
				if (at.getFunction().getName() == "is") {
					if (visited.add(t.mRep)) {
						Rule3(at);
					} else {
						// TODO: Rule 8 check if isC1(x) == true and isC2(x) == true, if so there is a conflict
					}
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
			Rule6(ct);
		}
		
		
		return null;
	}

	@Override
	public Clause computeConflictClause() {
		return null;
	}

	@Override
	public Literal getPropagatedLiteral() {
		if (!mPendingEqualities.isEmpty()) {
			SymmetricPair<CCTerm> eqPair = mPendingEqualities.poll();
			return mCClosure.createCCEquality(mClausifier.getStackLevel(), eqPair.getFirst(), eqPair.getSecond());
		}
		return null;
	}

	@Override
	public Clause getUnitClause(Literal literal) {
		CCEquality eq = (CCEquality) literal;
		Clause clause = buildUnitClause(eq.getLhs(), eq.getRhs(), literal);
		if (clause == null) clause = buildUnitClause(eq.getRhs(), eq.getLhs(), literal);
		assert clause != null : "no unit clause found";
		return clause;
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
		// TODO Auto-generated method stub
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
		// TODO Auto-generated method stub

	}

	@Override
	public Object[] getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}
	
	private void Rule3(ApplicationTerm at) {
		// check if there is already a constructor application equal to the argument
		Term arg = at.getParameters()[0];
		CCTerm argRep = mCClosure.getCCTermRep(arg);
		String consName = at.getFunction().getIndices()[0];
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
		addPendingEquality(new SymmetricPair<CCTerm>(argRep, consCCTerm));
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
					if (!c.getArgumentSorts()[i].getSortSymbol().isDatatype() || mInfinitSortsMap.get(c.getArgumentSorts()[i].getSortSymbol())) {
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
					mClausifier.createCCTerm(mTheory.term(mTheory.getFunctionSymbol(sel), ccterm.getFlatTerm()), SourceAnnotation.EMPTY_SOURCE_ANNOT);
				}
			}
		}
	}
	
	private void Rule5(CCTerm ccterm) {
		LinkedHashSet<String> selApps = findAllSelectorApplications(ccterm);
		SortSymbol sym = ccterm.mFlatTerm.getSort().getSortSymbol();
		for (Constructor c : ((DataType) sym).getConstructors()) {
			if (selApps.containsAll(Arrays.asList(c.getSelectors()))) {
				FunctionSymbol isFs = mTheory.getFunctionWithResult("is", new String[] {c.getName()}, null, new Sort[] {ccterm.getFlatTerm().getSort()});
				Term isTerm = mTheory.term(isFs, ccterm.mFlatTerm);
				if (mClausifier.getCCTerm(isTerm) == null) {
					mClausifier.createCCTerm(isTerm, SourceAnnotation.EMPTY_SOURCE_ANNOT);
				}
			}
		}
	}
	
	private void Rule6(CCTerm ccterm) {
		LinkedHashSet<String> isAppsIndices = new LinkedHashSet<>();
		CCParentInfo parInfo = ccterm.mRep.mCCPars;
		while (parInfo != null) {
			if (parInfo.mCCParents != null) {
				for (Parent p : parInfo.mCCParents) {
					FunctionSymbol fs = ((ApplicationTerm) p.getData().mFlatTerm).getFunction();
					if (fs.getName().equals("is")) isAppsIndices.add(fs.getIndices()[0]);
				}
			}
			parInfo = parInfo.mNext;
		}
		SortSymbol sym = ccterm.getFlatTerm().getSort().getSortSymbol();
		for (Constructor c : ((DataType) sym).getConstructors()) {
			if (!isAppsIndices.contains(c.getName())) return;
		}
		// TODO: prepare literal propagation isC1(x)\/isC2(x)\/...
	}
	
	private Clause buildUnitClause(CCTerm lhs, CCTerm rhs, Literal literal) {
		CongruencePath cp = new CongruencePath(mCClosure);
		ApplicationTerm lhsAt = lhs.getFlatTerm() instanceof ApplicationTerm ? (ApplicationTerm) lhs.getFlatTerm() : null;
		if (lhsAt == null) return null;
		if (lhsAt.getFunction().isSelector()) {
			CCTerm cons = findCorrespondingConstructor((CCAppTerm) lhs, rhs);
			assert cons != null : "no corresponding constructor found";
			cp.computePath(((CCAppTerm) lhs).getArg(), cons);
		} else if (lhsAt.getFunction().isConstructor()) {
			CCParentInfo rhsParInfo = rhs.mRep.mCCPars;
			while (rhsParInfo != null && cp.mAllLiterals.isEmpty()) {
				if (rhsParInfo.mCCParents != null) {
					for (Parent p : rhsParInfo.mCCParents) {
						FunctionSymbol fs = ((ApplicationTerm) p.getData().getFlatTerm()).getFunction();
						if (fs.getName().equals("is") && fs.getIndices()[0].equals(lhsAt.getFunction().getName())) {
							cp.computePath(p.getData(), mClausifier.getCCTerm(mTheory.mTrue));
							break;
						}
					}
				}
				rhsParInfo = rhsParInfo.mNext;
			}
		} else if (lhsAt.getFunction().getName().equals("is")) {
			CCTerm isArg = ((CCAppTerm) lhs).getArg();
			for (CCTerm mem : isArg.mRep.mMembers) {
				if (mem.getFlatTerm() instanceof ApplicationTerm && ((ApplicationTerm) mem.getFlatTerm()).getFunction().isConstructor()) {
					cp.computePath(isArg, mem);
					break;
				}
			}
		} else {
			return null;
		}
		
		//if (cp.mAllLiterals.isEmpty()) return null;
		
		LinkedHashSet<Literal> lits = new LinkedHashSet<>();
		lits.addAll(cp.mAllLiterals);
		Literal[] clauseLits = new Literal[lits.size() + 1];
		int i = 0;
		clauseLits[i++] = literal;
		for (Literal l : lits) {
			clauseLits[i++] = l.negate();
		}
		Clause clause = new Clause(clauseLits);
		// TODO: implement proof		
		return clause;
	}
	
	private CCTerm findCorrespondingConstructor(CCAppTerm selector, CCTerm equals) {
		ApplicationTerm at = (ApplicationTerm) selector.getFlatTerm();
		String funName = at.getFunction().getName();
		String[] selectors = mSelectorMap.get(funName).getSelectors();
		for (int i = 0; i < selectors.length; i++) {
			if (funName.equals(selectors[i])) {
				List<CCTerm> consApps = mCClosure.getAllFuncAppsForArg(mTheory.getFunctionSymbol(mSelectorMap.get(funName).getName()), equals, i);
				assert !consApps.isEmpty() : "no matching constructor applications found";
				CCTerm selArg = selector.getArg();
				for (CCTerm consTerm : consApps) {
					if (consTerm.mRep == selArg.mRep) {
						return consTerm;
					}
				}
			}
		}
		return null;
	}
	
	private LinkedHashSet<String> findAllSelectorApplications(CCTerm ccterm) {
		LinkedHashSet<String> selApps = new LinkedHashSet<>();
		CCParentInfo parInfo = ccterm.mRep.mCCPars;
		while (parInfo != null) {
			if (parInfo.mCCParents != null) {
				for (Parent p : parInfo.mCCParents) {
					FunctionSymbol fun = ((ApplicationTerm) p.getData().getFlatTerm()).getFunction();
					if (fun.isSelector()) selApps.add(fun.getName());
				}
			}
			parInfo = parInfo.mNext;
		}
		return selApps;
	}

}
