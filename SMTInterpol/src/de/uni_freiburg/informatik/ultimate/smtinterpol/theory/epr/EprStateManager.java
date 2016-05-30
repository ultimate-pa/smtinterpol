package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprBaseClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprDerivedClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprGroundUnitClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprNonUnitClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprQuantifiedUnitClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprUnitClause;

public class EprStateManager {
	
	private Stack<EprState> mEprStateStack = new Stack<EprState>();
	private Stack<Object> mLiteralStack = new Stack<Object>();
	
	private EprState baseState;
	
	
	HashMap<Set<Literal>, EprNonUnitClause> mLiteralToClauses = new HashMap<Set<Literal>, EprNonUnitClause>();
	public EqualityManager mEqualityManager;
	private EprTheory mEprTheory;
	private Theory mTheory;
	private CClosure mCClosure; //TODO: clean up --> where to carry this through clauses??
	
	HashSet<EprPredicate> mAllEprPredicates = new HashSet<EprPredicate>();
	
	public EprStateManager(EprTheory eprTheory) {
		baseState = new EprState();
		mEprStateStack.push(baseState);
		mEprTheory = eprTheory;
		mEqualityManager =  eprTheory.getEqualityManager();
		mTheory = eprTheory.getTheory();
		mCClosure = eprTheory.getCClosure();
	}

	public void beginScope(Object literal) {
		mLiteralStack.push(literal);
		mEprStateStack.push(new EprState(mEprStateStack.peek()));
	}

	/**
	 * Revert everything that followed from setting literal
	 *  - pop the corresponding EprState
	 *  - revert the fulfillability status of the remaining epr-clauses (in lower states)
	 * @param literal
	 */
	public void endScope(Object literal) {
		mEprStateStack.pop();
		Object popped = mLiteralStack.pop();
//		assert literal.equals(popped);
		
	}

	public Clause setGroundLiteral(Literal literal) {
		
		EprGroundPredicateAtom atom = (EprGroundPredicateAtom) literal.getAtom();
		
		// is there a conflict with one of the currently set quantified literals??
		for (EprQuantifiedUnitClause l : getSetLiterals(literal.getSign() == 1, atom.eprPredicate)) {
			TTSubstitution sub = l.getPredicateAtom().getArgumentsAsTermTuple().match(atom.getArgumentsAsTermTuple(), mEqualityManager);
			if (sub != null) {
				EprClause conflict =  l.getExplanation().instantiateClause(null, sub);
				return conflict;
			}
		}
		// is there a conflict with one of the currently set points 
		// (taking into account the current equalities between constants)
		HashSet<TermTuple> possibleConflictPoints = this.getPoints(literal.getSign() != 1, atom.eprPredicate);
		for (TermTuple point : possibleConflictPoints) {
			TTSubstitution sub = point.match(atom.getArgumentsAsTermTuple(), mEqualityManager);
			if (sub != null) {
				// build conflict clause
				ArrayList<Literal> confLits = new ArrayList<Literal>();

				confLits.add(literal.negate());

				EprGroundPredicateAtom atomOfPoint = atom.eprPredicate.getAtomForPoint(point);
				confLits.add(literal.getSign() != 1 ? atomOfPoint.negate() : atomOfPoint);

				confLits.addAll(getDisequalityChainsFromSubstitution(sub, point.terms, atom.getArguments()));
				
				Clause conflict = new Clause(confLits.toArray(new Literal[confLits.size()]));
				return conflict;
			}
		}	
		
		// if there is no conflict, set it..
		mEprStateStack.peek().setPoint(
				literal.getSign() == 1, 
				(EprGroundPredicateAtom) literal.getAtom());
		return null;
	}

	/**
	 * Given a substitution and to Term arrays, computes a list of disequalities as follows:
	 * For every position in the two arrays where the substitution needed an equality for unification, adds 
	 *    all the set CCEqualities to the result that are needed for establishing that unifying equality.
	 * @param sub a substitution that unifies terms1 and terms2, possibly with the use of ground equalities
	 * @param terms1 Term array that is unified with terms2 through sub
	 * @param terms2 Term array that is unified with terms1 through sub
	 * @return all the equalities that are currently set through the DPLLEngine 
	 *	         that are needed for the unification of terms1 and terms2
	 */
	private ArrayList<Literal> getDisequalityChainsFromSubstitution(TTSubstitution sub, Term[] terms1,
			Term[] terms2) {
		ArrayList<Literal> disequalityChain = new ArrayList<Literal>();
		for (int i = 0; i < terms1.length; i++) {
			if (!(terms1[i] instanceof ApplicationTerm ) || !(terms2[i] instanceof ApplicationTerm)) 
				continue;
			ApplicationTerm pointAt = (ApplicationTerm) terms1[i];
			ApplicationTerm atomAt = (ApplicationTerm)  terms2[i];
			for (CCEquality cceq : sub.getEqPathForEquality(pointAt, atomAt)) {
				disequalityChain.add(cceq.negate());
			}
		}
		return disequalityChain;
	}
	
	public Clause setQuantifiedLiteralWithExceptions(EprQuantifiedUnitClause eqlwe) {
		mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): setting Quantified literal: " + eqlwe);

		
		mEprStateStack.peek().setQuantifiedLiteralWithExceptions(eqlwe);
		
		
		//TODO: possibly do a more efficient consistency check
		// i.e. only wrt the currently set literal
		Clause conflict = checkConsistency();
		if (conflict != null) {
			mEprStateStack.peek().unsetQuantifiedLiteralWithExceptions(eqlwe);
		}

		//TODO:
		// possibly update all literal states in clauses, right?..
		return conflict;
	}
	
	public Clause setGroundEquality(CCEquality eq) {
		ApplicationTerm f = (ApplicationTerm) eq.getSMTFormula(mTheory);
		ApplicationTerm lhs = (ApplicationTerm) f.getParameters()[0];
		ApplicationTerm rhs = (ApplicationTerm) f.getParameters()[1];
	
		mEqualityManager.addEquality(lhs, rhs, (CCEquality) eq);
	
	
		// is there a conflict with currently set points or quantifiedy literals?
		Clause conflict = checkConsistency();
		
		//TODO:
		// possibly update all literal states in clauses, right?..
		//  (..if there is no conflict?..)

		return conflict;
	}
	
	/**
	 * Checks for all eprPredicates if their current state is consistent.
	 * The current state means points that are set and quantified literals that are set.
	 * @return conflict clause if there is a conflict, null otherwise
	 */
	public Clause checkConsistency() {
		
		//TODO: make sure that i case of a
		
		for (EprPredicate pred : mAllEprPredicates) {
			for (EprQuantifiedUnitClause eqwlePos : getSetLiterals(true, pred)) {
				EprQuantifiedUnitClause arPosUnit = eqwlePos.getFreshAlphaRenamedVersion();
				TermTuple ttPos = arPosUnit.getPredicateAtom().getArgumentsAsTermTuple();
				for (EprQuantifiedUnitClause eqwleNeg : getSetLiterals(false, pred)) {
					TermTuple ttNeg = eqwleNeg.getPredicateAtom().getArgumentsAsTermTuple();
					TTSubstitution sub = ttNeg.match(ttPos, mEqualityManager);
					if (sub != null) {
						return arPosUnit.getExplanation().instantiateClause(null, sub);
					}
				}
				
				for (TermTuple pointNeg : getPoints(false, pred)) {
					TTSubstitution sub = pointNeg.match(ttPos, mEqualityManager);
					if (sub != null) {
						EprClause conflict =  arPosUnit.getExplanation().instantiateClause(null, sub, 
								getDisequalityChainsFromSubstitution(sub, pointNeg.terms, 
										arPosUnit.getPredicateAtom().getArguments()));
						return conflict;
					}
				}
			}
			for (TermTuple pointPos : getPoints(true, pred)) {
				for (EprQuantifiedUnitClause eqwleNeg : getSetLiterals(false, pred)) {
					TermTuple ttNeg = eqwleNeg.getPredicateAtom().getArgumentsAsTermTuple();
					TTSubstitution sub = ttNeg.match(pointPos, mEqualityManager);
					if (sub != null) {
						return eqwleNeg.getExplanation().instantiateClause(null, sub);
					}
				}
				
				for (TermTuple pointNeg : getPoints(false, pred)) {
					TTSubstitution sub = pointNeg.match(pointPos, mEqualityManager);
					if (sub != null) {
						// build conflict clause
						ArrayList<Literal> confLits = new ArrayList<Literal>();

						confLits.addAll(getDisequalityChainsFromSubstitution(sub, pointPos.terms, pointNeg.terms));
						
						confLits.add(pred.getAtomForPoint(pointPos).negate());
						confLits.add(pred.getAtomForPoint(pointNeg));

						return new Clause(confLits.toArray(new Literal[confLits.size()]));
					}
				}
			}
		
		}

		return null;
	}

	public HashSet<TermTuple> getPoints(boolean positive, EprPredicate pred) {
		//TODO: some caching here?
		HashSet<TermTuple> result = new HashSet<TermTuple>();
		for (EprState es : mEprStateStack) {
			EprPredicateModel model = es.mPredicateToModel.get(pred);
			if (model == null) //maybe not all eprStates on the stack know the predicate
				continue;
			if (positive)
				result.addAll(model.mPositivelySetPoints);
			else
				result.addAll(model.mNegativelySetPoints);
		}
		return result;
	}

	public ArrayList<EprQuantifiedUnitClause> getSetLiterals(boolean positive, EprPredicate pred) {
		//TODO: some caching here?
		ArrayList<EprQuantifiedUnitClause> result = new ArrayList<EprQuantifiedUnitClause>();
		for (EprState es : mEprStateStack) {
			EprPredicateModel model = es.mPredicateToModel.get(pred);
			if (model == null) //maybe not all eprStates on the stack know the predicate
				continue;
			if (positive)
				result.addAll(model.mPositivelySetQuantifiedLitsWE);
			else
				result.addAll(model.mNegativelySetQuantifiedLitsWE);
		}
		return result;
	
	}

	public ArrayList<EprQuantifiedUnitClause> getSetLiterals(EprPredicate eprPredicate) {
		//TODO: some caching here?
		ArrayList<EprQuantifiedUnitClause> result = new ArrayList<EprQuantifiedUnitClause>();
		result.addAll(getSetLiterals(true, eprPredicate));
		result.addAll(getSetLiterals(false, eprPredicate));
		return result;
	}

	public void addNewEprPredicate(EprPredicate pred) {
		 mEprStateStack.peek().addNewEprPredicate(pred);
		 mAllEprPredicates.add(pred);
	}

	/**
	 * Adds a clause that is derivable in the current state.
	 * @param dc
	 */
	public boolean addDerivedClause(EprNonUnitClause dc) {
		mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): adding derived clause " + dc);
		return mEprStateStack.peek().addDerivedClause(dc);
	}

	public boolean addBaseClause(EprNonUnitClause bc) {
		mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): adding base clause " + bc);
		return mEprStateStack.peek().addBaseClause(bc);
	}

	public ArrayList<EprNonUnitClause> getTopLevelDerivedClauses() {
		return mEprStateStack.peek().getDerivedClauses();
	}

	public HashSet<EprNonUnitClause> getAllClauses() {
		HashSet<EprNonUnitClause> allClauses = new HashSet<EprNonUnitClause>();
		for (EprState es : mEprStateStack) {
			allClauses.addAll(es.getBaseClauses());
			allClauses.addAll(es.getDerivedClauses());
		}
		return allClauses;
	}

	public HashSet<EprNonUnitClause> getFulfilledClauses() {
		HashSet<EprNonUnitClause> fulfilledClauses = new HashSet<EprNonUnitClause>();
		for (EprNonUnitClause ec : getAllClauses())
			if (ec.isFulfilled())
				fulfilledClauses.add(ec);
		return fulfilledClauses;
	}
	
	public HashSet<EprNonUnitClause> getNotFulfilledClauses() {
		HashSet<EprNonUnitClause> notFulfilledClauses = new HashSet<EprNonUnitClause>();
		for (EprNonUnitClause ec : getAllClauses())
			if (!ec.isFulfilled())
				notFulfilledClauses.add(ec);
		return notFulfilledClauses;
	}

	public HashSet<EprClause> getConflictClauses() {
		HashSet<EprClause> result = new HashSet<EprClause>();
		for (EprState es : mEprStateStack) {
			result.addAll(es.getConflictClauses());
		}
		return result;
	}

	/**
	 * makes sure that for the same set of literals only one clause is constructed.
	 * Note that this may return a EprDerivedClause -- if there already is one for the set of Literals
	 */
	public EprNonUnitClause getBaseClause(Set<Literal> newLits, Theory theory) {
		EprNonUnitClause result = mLiteralToClauses.get(newLits);
		if (result == null) {
			result = new EprBaseClause(newLits.toArray(new Literal[newLits.size()]), mEprTheory);
			mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): creating new base clause " + result);
			mLiteralToClauses.put(newLits, result);
		}
		return result;
	}
	
	/**
	 * makes sure that for the same set of literals only one clause is constructed.
	 * Note that this may return a EprBaseClause -- if there already is one for the set of Literals
	 */
	public EprClause getDerivedClause(Set<Literal> newLits, EprTheory eprTheory, Object explanation) {
		EprNonUnitClause result = mLiteralToClauses.get(newLits);
		if (result == null) {
			result = new EprDerivedClause(newLits.toArray(new Literal[newLits.size()]), eprTheory, explanation);
			mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): creating new derived clause " + result);
			mLiteralToClauses.put(newLits, result);
		}
		return result;
	}

	/**
	 * TODO: rework this some time.
	 * Checks if the given literal is already set, or if something stronger is set.
	 * @param unifiedUnitLiteral
	 * @return
	 */
	public boolean isSubsumedInCurrentState(EprUnitClause euc) { //TODO possibly this needs to work on a QuantifiedLitWExcptns
		if (euc instanceof EprGroundUnitClause) {
			Literal lit = ((EprGroundUnitClause) euc).getPredicateLiteral();
			if (lit.getAtom().getDecideStatus() == lit) { // is it set in DPLL?
				return true;
			}
			if (!(lit.getAtom() instanceof EprPredicateAtom))
				return false;

			boolean isPositive = lit.getSign() == 1;
			EprPredicateAtom atom = (EprPredicateAtom) lit.getAtom();

			for (EprQuantifiedUnitClause sl : this.getSetLiterals(isPositive, atom.eprPredicate)) {
				TermTuple slTT = sl.getFreshAlphaRenamedVersion().getPredicateAtom().getArgumentsAsTermTuple();
				TermTuple tt = atom.getArgumentsAsTermTuple();
				TTSubstitution sub = slTT.match(tt, mEqualityManager);
				if (slTT.isEqualOrMoreGeneralThan(tt))
					return true;
			}
			return false;
		} else {
			assert false : "TODO: implement this case";
			return false;
		}
	}
	
	public CClosure getCClosure() {
		return mCClosure;
	}

	public HashSet<EprPredicate> getAllEprPredicates() {
		assert false : "TODO: check: is the field updated correctly??";
		return mAllEprPredicates;
	}
	
	/**
	 * TODO: implement one solution for constant handling!
	 * @param constants
	 */
	public void addConstants(HashSet<ApplicationTerm> constants) {
		mEprStateStack.peek().addConstants(constants);
	}
	
//	public HashSet<ApplicationTerm> getAllConstants(Sort sort) {
	public HashSet<ApplicationTerm> getAllConstants() {
		HashSet<ApplicationTerm> result = new HashSet<ApplicationTerm>();
		//the following comment has the insufficient solution
		//  -- only the constants we have seen in a clause so far.
		//     we need all those which are/were/will be used in the current push/pop scope
		//     --> ask the Theory for all declared functions instead
//		for (EprState s : mEprStateStack)
//			result.addAll(s.getUsedConstants());
		
		for (Entry<String, FunctionSymbol> en : mTheory.getDeclaredFuns().entrySet()) {
			FunctionSymbol fs = en.getValue();
			if (fs.getParameterSorts().length == 0) 
//					&& fs.getReturnSort().equals(sort))
				result.add(mTheory.term(fs));
		}
		

		return result;
	}

	public ArrayList<TTSubstitution> getAllInstantiations(HashSet<TermVariable> freeVars, HashSet<ApplicationTerm> constants) {
		ArrayList<TTSubstitution> insts = new ArrayList<TTSubstitution>();
//		ArrayList<ApplicationTerm> allConstantsAsList = new ArrayList<>(getAllConstants());
		insts.add(new TTSubstitution());

		for (TermVariable tv : freeVars) {
			ArrayList<TTSubstitution> instsNew = new ArrayList<TTSubstitution>();
			for (TTSubstitution sub : insts) {
//				for (ApplicationTerm con : allConstantsAsList) {
				for (ApplicationTerm con : constants) {
					if (con.getSort().equals(tv.getSort())) {
						TTSubstitution newSub = new TTSubstitution(sub);
						newSub.addSubs(con, tv);
						instsNew.add(newSub);
					}
				}
			}
			insts = instsNew;
		}
		return insts;
	}
}
