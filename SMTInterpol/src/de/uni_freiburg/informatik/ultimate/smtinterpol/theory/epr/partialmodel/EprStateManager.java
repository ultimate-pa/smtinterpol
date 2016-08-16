package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EqualityManager;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprBaseClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprClauseOld;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprDerivedClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprGroundUnitClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprNonUnitClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprQuantifiedUnitClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprUnitClause;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashSet;

/**
 * This class is responsible for managing everything that is connected to the
 * current decide state of the EprTheory.
 * This entails:
 *  - managing the Epr decide stack according to push/pop and setLiteral commands
 *   as well as internal propagations and decisions
 *  - telling clauses to update their states (or so..)
 * 
 * @author nutz
 */
public class EprStateManager {

	Stack<EprPushState> mPushStateStack = new Stack<EprPushState>();
	
	/**
	 * Remembers from which sets of literals an EprClause has already been 
	 * constructed (and which).
	 */
	ScopedHashMap<Set<Literal>, EprClause> mLiteralsToClause = new ScopedHashMap<Set<Literal>, EprClause>();

	public EqualityManager mEqualityManager;
	private EprTheory mEprTheory;
	private Theory mTheory;
	private CClosure mCClosure;
	
	ScopedHashSet<EprPredicate> mAllEprPredicates = new ScopedHashSet<EprPredicate>();
	
	/**
	 * Remembers for each DPLLAtom in which EprClauses it occurs (if any).
	 */
	HashMap<DPLLAtom, HashSet<EprClause>> mDPLLAtomToClauses = 
			new HashMap<DPLLAtom, HashSet<EprClause>>();

	
	public EprStateManager(EprTheory eprTheory) {
//		baseState = new EprState();
//		mEprStateStack.push(baseState);

		mPushStateStack.add(new EprPushState());

		mEprTheory = eprTheory;
		mEqualityManager =  eprTheory.getEqualityManager();
		mTheory = eprTheory.getTheory();
		mCClosure = eprTheory.getCClosure();
	}


	public void push() {
		mPushStateStack.push(new EprPushState());
		mLiteralsToClause.beginScope();
		mAllEprPredicates.beginScope();
	}
	
	public void pop() {
		mPushStateStack.pop();
		mLiteralsToClause.endScope();
		mAllEprPredicates.endScope();
	}

	////////////////// 
	////////////////// methods that change the epr solver state (state of clauses and/or decide stack)
	////////////////// 

	public Clause setEprGroundLiteral(Literal literal) {
		
		EprGroundPredicateAtom atom = (EprGroundPredicateAtom) literal.getAtom();
		EprPredicate pred = atom.getEprPredicate();
		
		return null;
		// old:
//		// is there a conflict with one of the currently set quantified literals??
//		for (EprQuantifiedUnitClause l : getSetLiterals(literal.getSign() == 1, atom.eprPredicate)) {
//			TTSubstitution sub = l.getPredicateAtom().getArgumentsAsTermTuple().match(atom.getArgumentsAsTermTuple(), mEqualityManager);
//			if (sub != null) {
//				EprClauseOld conflict =  l.getExplanation().instantiateClause(null, sub);
//				return conflict;
//			}
//		}
//		// is there a conflict with one of the currently set points 
//		// (taking into account the current equalities between constants)
//		HashSet<TermTuple> possibleConflictPoints = this.getPoints(literal.getSign() != 1, atom.eprPredicate);
//		for (TermTuple point : possibleConflictPoints) {
//			TTSubstitution sub = point.match(atom.getArgumentsAsTermTuple(), mEqualityManager);
//			if (sub != null) {
//				// build conflict clause
//				ArrayList<Literal> confLits = new ArrayList<Literal>();
//
//				confLits.add(literal.negate());
//
//				EprGroundPredicateAtom atomOfPoint = atom.eprPredicate.getAtomForPoint(point);
//				confLits.add(literal.getSign() != 1 ? atomOfPoint.negate() : atomOfPoint);
//
//				confLits.addAll(getDisequalityChainsFromSubstitution(sub, point.terms, atom.getArguments()));
//				
//				Clause conflict = new Clause(confLits.toArray(new Literal[confLits.size()]));
//				return conflict;
//			}
//		}	
//		
//		// if there is no conflict, set it..
//		mEprStateStack.peek().setPoint(
//				literal.getSign() == 1, 
//				(EprGroundPredicateAtom) literal.getAtom());
//		return null;
	}
	
	public void unsetEprGroundLiteral(Literal literal) {
		assert false : "TODO: write this method (probably after setGroundLiteral has been written)";
	}
	
	/**
	 * Inform all the EprClauses that contain the atom (not only the
	 * literal!) that they have to update their fulfillment state.
	 */
	public void updateClausesOnSetDpllLiteral(Literal literal) {
		HashSet<EprClause> clauses = 
				this.getClausesThatContainAtom(literal.getAtom());
		if (clauses != null) {
			for (EprClause ec : clauses) {
				ec.updateStateWrtDpllLiteral(literal);
			}
		}
	}

	/**
	 * Informs the clauses that contain the literal's atom that
	 * it is backtracked by the DPLLEngine.
	 * @param literal
	 */
	public void updateClausesOnBacktrackDpllLiteral(Literal literal) {
		HashSet<EprClause> clauses = 
				this.getClausesThatContainAtom(literal.getAtom());
		if (clauses != null) {
			for (EprClause ec : clauses) {
				ec.backtrackStateWrtDpllLiteral(literal);
			}
		}
	
	}


	
	//////////////////////////////////// old, perhaps obsolete, stuff, from here on downwards /////////////////////////////////////////
	
	public void updateAtomToClauses(DPLLAtom atom, EprClause c) {
		HashSet<EprClause> clauses = mDPLLAtomToClauses.get(atom);
		if (clauses == null) {
			clauses = new HashSet<EprClause>();
			mDPLLAtomToClauses.put(atom, clauses);
		}
		clauses.add(c);
	}


	////////////////// 
	////////////////// methods for management of basic data structures
	////////////////// 

	public HashSet<EprClause> getClausesThatContainAtom(DPLLAtom atom) {
		return mDPLLAtomToClauses.get(atom);
	}


	public void addNewEprPredicate(EprPredicate pred) {
	//		 mEprStateStack.peek().addNewEprPredicate(pred);
	//		 mAllEprPredicates.add(pred);
	//		mPushStateStack.peek().addEprPredicate(pred);
			mAllEprPredicates.add(pred);
		}


	public ScopedHashSet<EprPredicate> getAllEprPredicates() {
	//		assert false : "TODO: check: is the field updated correctly??";
	//		return mAllEprPredicates;
			return mAllEprPredicates;
		}


	public void addClause(HashSet<Literal> literals) {
		EprClause newClause = this.getClause(literals);
		mPushStateStack.peek().addClause(newClause);
		
		for (Literal li : literals) {
			updateAtomToClauses(li.getAtom(), newClause);
		}
	}



	/**
	 * makes sure that for the same set of literals only one clause is constructed.
	 * Note that this may return a EprDerivedClause -- if there already is one for the set of Literals
	 * (copy from the old getBaseClause method)
	 */
	private EprClause getClause(Set<Literal> newLits) {
		EprClause result = mLiteralsToClause.get(newLits);
		if (result == null) {
			result = new EprClause(newLits, mEprTheory);
			mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): creating new clause " + result);
			mLiteralsToClause.put(newLits, result);
		} else {
			mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): clause has been added before " + result);
		}
		return result;
	}



	HashMap<Set<Literal>, EprNonUnitClause> mLiteralToClauses = new HashMap<Set<Literal>, EprNonUnitClause>();

	private Stack<EprState> mEprStateStack = new Stack<EprState>();
	
	// contains the ground literal currently set by the DPLLEngine for
	// every scope that was created by EprTheory.setLiteral(), and the 
	// word "push" for all push scopes
	// (not used at the moment..)
	private Stack<Object> mLiteralStack = new Stack<Object>();
	
	private EprState baseState;
	


	@Deprecated
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
	@Deprecated
	public void endScope(Object literal) {
		mEprStateStack.pop();
		Object popped = mLiteralStack.pop();
//		assert literal.equals(popped);
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
	@Deprecated
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
	
	@Deprecated
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
	
	@Deprecated
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
	
	@Deprecated
	public void unsetGroundEquality(CCEquality eq) {
		ApplicationTerm f = (ApplicationTerm) eq.getSMTFormula(mTheory);
		ApplicationTerm lhs = (ApplicationTerm) f.getParameters()[0];
		ApplicationTerm rhs = (ApplicationTerm) f.getParameters()[1];

		mEqualityManager.backtrackEquality(lhs, rhs);
	}
	
	/**
	 * Checks for all eprPredicates if their current state is consistent.
	 * The current state means points that are set and quantified literals that are set.
	 * @return conflict clause if there is a conflict, null otherwise
	 */
	@Deprecated
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
						EprClauseOld conflict =  arPosUnit.getExplanation().instantiateClause(null, sub, 
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

	@Deprecated
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

	@Deprecated
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

	@Deprecated
	public ArrayList<EprQuantifiedUnitClause> getSetLiterals(EprPredicate eprPredicate) {
		//TODO: some caching here?
		ArrayList<EprQuantifiedUnitClause> result = new ArrayList<EprQuantifiedUnitClause>();
		result.addAll(getSetLiterals(true, eprPredicate));
		result.addAll(getSetLiterals(false, eprPredicate));
		return result;
	}



	/**
	 * Adds a clause that is derivable in the current state.
	 * @param dc
	 */
	@Deprecated
	public boolean addDerivedClause(EprNonUnitClause dc) {
		mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): adding derived clause " + dc);
		return mEprStateStack.peek().addDerivedClause(dc);
	}

	@Deprecated
	public boolean addBaseClause(EprNonUnitClause bc) {
		mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): adding base clause " + bc);

		if (mEprTheory.isGroundAllMode()) {
			addGroundClausesForNewEprClause(bc);
		}

		return mEprStateStack.peek().addBaseClause(bc);
	}

	@Deprecated
	public ArrayList<EprNonUnitClause> getTopLevelDerivedClauses() {
		return mEprStateStack.peek().getDerivedClauses();
	}

	@Deprecated
	public HashSet<EprNonUnitClause> getAllClauses() {
		HashSet<EprNonUnitClause> allClauses = new HashSet<EprNonUnitClause>();
		for (EprState es : mEprStateStack) {
			allClauses.addAll(es.getBaseClauses());
			allClauses.addAll(es.getDerivedClauses());
		}
		return allClauses;
	}

	@Deprecated
	public HashSet<EprNonUnitClause> getFulfilledClauses() {
		HashSet<EprNonUnitClause> fulfilledClauses = new HashSet<EprNonUnitClause>();
		for (EprNonUnitClause ec : getAllClauses())
			if (ec.isFulfilled())
				fulfilledClauses.add(ec);
		return fulfilledClauses;
	}
	
	@Deprecated
	public HashSet<EprNonUnitClause> getNotFulfilledClauses() {
		HashSet<EprNonUnitClause> notFulfilledClauses = new HashSet<EprNonUnitClause>();
		for (EprNonUnitClause ec : getAllClauses())
			if (!ec.isFulfilled())
				notFulfilledClauses.add(ec);
		return notFulfilledClauses;
	}

	@Deprecated
	public HashSet<EprClauseOld> getConflictClauses() {
		HashSet<EprClauseOld> result = new HashSet<EprClauseOld>();
		for (EprState es : mEprStateStack) {
			result.addAll(es.getConflictClauses());
		}
		return result;
	}

	/**
	 * makes sure that for the same set of literals only one clause is constructed.
	 * Note that this may return a EprDerivedClause -- if there already is one for the set of Literals
	 */
	@Deprecated
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
	@Deprecated
	public EprClauseOld getDerivedClause(Set<Literal> newLits, EprTheory eprTheory, Object explanation) {
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
	@Deprecated
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

			for (EprQuantifiedUnitClause sl : this.getSetLiterals(isPositive, atom.getEprPredicate())) {
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
	
	@Deprecated
	public CClosure getCClosure() {
		return mCClosure;
	}


	
	/**
	 * @param constants
	 */
	@Deprecated
	public void addConstants(HashSet<ApplicationTerm> constants) {
		HashSet<ApplicationTerm> reallyNewConstants = new HashSet<ApplicationTerm>();
		if (mEprTheory.isGroundAllMode()) {
			for (ApplicationTerm newConstant : constants) {
				if (!getAllConstants().contains(newConstant))
					reallyNewConstants.add(newConstant);
			}
		}
		addGroundClausesForNewConstant(reallyNewConstants);
		
		mEprStateStack.peek().addConstants(constants);
	}
	
	@Deprecated
	public HashSet<ApplicationTerm> getAllConstants() {
		HashSet<ApplicationTerm> result = new HashSet<ApplicationTerm>();

		for (EprState s : mEprStateStack)
			result.addAll(s.getUsedConstants());
		
		return result;
	}

	/**
	 * Computes all the instantiations of the variables in freeVars that
	 * are added to the set of instantiations of oldConstants by adding one
	 * or more constants from newConstants.
	 * In other words: compute all instantiations of freeVars where a new constant occurs
	 * at least once.
	 * 
	 * @param freeVars
	 * @param newConstant
	 * @param oldConstants
	 * @return
	 */
	@Deprecated
	public ArrayList<TTSubstitution> getAllInstantiationsForNewConstant(
			HashSet<TermVariable> freeVars, 
			HashSet<ApplicationTerm> newConstants,
			HashSet<ApplicationTerm> oldConstants) {
		
		ArrayList<TTSubstitution> instsWithNewConstant = 
				new ArrayList<TTSubstitution>();
		ArrayList<TTSubstitution> instsWithOutNewConstant = 
				new ArrayList<TTSubstitution>();
		
		HashSet<ApplicationTerm> allConstants = new HashSet<ApplicationTerm>(oldConstants);
		allConstants.addAll(newConstants);

		instsWithNewConstant.add(new TTSubstitution());
		instsWithOutNewConstant.add(new TTSubstitution());

		for (TermVariable tv : freeVars) {
			ArrayList<TTSubstitution> instsNewWNC = new ArrayList<TTSubstitution>();
			ArrayList<TTSubstitution> instsNewWONC = new ArrayList<TTSubstitution>();
			for (TTSubstitution sub : instsWithNewConstant) {
				for (ApplicationTerm con : allConstants) {
					if (con.getSort().equals(tv.getSort())) {
						TTSubstitution newSub = new TTSubstitution(sub);
						newSub.addSubs(con, tv);
						instsNewWNC.add(newSub);
					}
				}
			}

			for (TTSubstitution sub : instsWithOutNewConstant) {
				for (ApplicationTerm con : oldConstants) {
					if (con.getSort().equals(tv.getSort())) {
						TTSubstitution newSub = new TTSubstitution(sub);
						newSub.addSubs(con, tv);
						instsNewWONC.add(newSub);
					}
				}
				for (ApplicationTerm newConstant : newConstants) {
					if (newConstant.getSort().equals(tv.getSort())) {
						TTSubstitution newSub = new TTSubstitution(sub);
						newSub.addSubs(newConstant, tv);
						instsNewWNC.add(newSub);
					}
				}
			}
			instsWithNewConstant = instsNewWNC;
			instsWithOutNewConstant = instsNewWONC;
		}
		return instsWithNewConstant;
	}

	@Deprecated
	public ArrayList<TTSubstitution> getAllInstantiations(
			HashSet<TermVariable> freeVars, 
			HashSet<ApplicationTerm> constants) {
		ArrayList<TTSubstitution> insts = new ArrayList<TTSubstitution>();
		insts.add(new TTSubstitution());

		for (TermVariable tv : freeVars) {
			ArrayList<TTSubstitution> instsNew = new ArrayList<TTSubstitution>();
			for (TTSubstitution sub : insts) {
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
	
	@Deprecated
	private void addGroundClausesForNewConstant(HashSet<ApplicationTerm> newConstants) {
		ArrayList<Literal[]> groundings = new ArrayList<Literal[]>();
		for (EprNonUnitClause c : getAllClauses())  {
				groundings.addAll(
						c.computeAllGroundings(
								getAllInstantiationsForNewConstant(
										c.getFreeVars(), 
										newConstants, 
										this.getAllConstants())));
		}
		addGroundClausesToDPLLEngine(groundings);
	}

	@Deprecated
	private void addGroundClausesForNewEprClause(EprNonUnitClause newEprClause) {
		List<Literal[]> groundings = 		
						newEprClause.computeAllGroundings(
								getAllInstantiations(
										newEprClause.getFreeVars(), 
										this.getAllConstants()));
		addGroundClausesToDPLLEngine(groundings);
	}

	@Deprecated
	private void addGroundClausesToDPLLEngine(List<Literal[]> groundings) {
		for (Literal[] g : groundings) {
//			//TODO not totally clear if addFormula is the best way, but addClause(..) has
//			//  visibility package right now..
			mEprTheory.getClausifier().getEngine().addFormulaClause(g, null); // TODO: proof (+ hook?)
			
			mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): added ground clause " + Arrays.toString(g));
		}
	}

}
