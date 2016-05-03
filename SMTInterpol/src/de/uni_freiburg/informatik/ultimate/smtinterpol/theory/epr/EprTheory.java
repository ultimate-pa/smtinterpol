package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom.TrueAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprGroundUnitClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprNonUnitClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprQuantifiedUnitClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprUnitClause;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashSet;

public class EprTheory implements ITheory {

	HashMap<FunctionSymbol, EprPredicate> mFunctionSymbolToEprPredicate = new HashMap<>();

	HashMap<Literal, HashSet<EprNonUnitClause>> mLiteralToClauses = new HashMap<>();
	
	ArrayDeque<Literal> mGroundLiteralsToPropagate = new ArrayDeque<Literal>();

	private Theory mTheory;
	private DPLLEngine mEngine;

	HashMap<Object, HashMap<TermVariable, Term>> mBuildClauseToAlphaRenamingSub = 
			new HashMap<Object, HashMap<TermVariable,Term>>();
	
	EprStateManager mStateManager;

	/**
	 * if we propagate a ground literal we have to be able to give a unit clause
	 * that explains the literal
	 */
	private HashMap<Literal, Clause> mPropLitToExplanation = new HashMap<>();

	HashSet<DPLLAtom> mAtomsAddedToDPLLEngine = new HashSet<>();
	
	EqualityManager mEqualityManager;

	private boolean mConflict;

	public EprTheory(Theory th, DPLLEngine engine, CClosure cClosure) {
		mTheory = th;
		mEngine = engine;

		mEqualityManager = new EqualityManager();
		mStateManager = new EprStateManager(mEqualityManager, mTheory, cClosure);
	}

	@Override
	public Clause startCheck() {
		System.out.println("EPRDEBUG: startCheck");
		return null;
	}

	@Override
	public void endCheck() {
		System.out.println("EPRDEBUG: endCheck");
	}

	@Override
	public Clause setLiteral(Literal literal) {
		System.out.println("EPRDEBUG: setLiteral " + literal);
		
		mStateManager.beginScope(literal);

		// does this literal occur in any of the EprClauses?
		// --> then check for satisfiability
		//   return a conflict clause in case
		//   possibly do (or cache) propagations
		// --> otherwise update the predicate model (held in the corresponding EprPredicate) accordingly

		DPLLAtom atom = literal.getAtom();
		
		if (atom instanceof EprGroundPredicateAtom) {
			// literal is of the form (P c1 .. cn) (no quantification, but an EprPredicate)
			// it being set by the DPLLEngine (the quantified EprPredicateAtoms are not known to the DPLLEngine)
			

			//current Arbeitsteilung concerning EprTheory solver state information:
			// EprStateManager deals with 
			//  - single points in the predicates
			//  - which clauses are derived clauses at which level
			//  - which quantified literals (with exceptions) are set
			// EprTheory deals with EprClauses, i.e.:
			//  - updates the fulfillabilityState of all currently active clauses' literals
			//  - updates its own set of currently active clauses (derived or not) with help of the EprStateManager

			Clause conflict = mStateManager.setGroundLiteral(literal);
			if (conflict != null)
				return conflict; // then act as if the literal is not set, right?

			setGroundLiteralInClauses(literal);

			return null;
		} else if (atom instanceof EprEqualityAtom 
				|| atom instanceof EprQuantifiedPredicateAtom) {
			assert false : "DPLLEngine is setting a quantified EprAtom --> this cannot be..";
			return null;
		} else if (atom instanceof CCEquality) {
			if (literal.getSign() == 1) {
				CCEquality eq = (CCEquality) atom;
				
				return mStateManager.setGroundEquality((CCEquality) atom);
			}
			// TODO do disequalities have an impact for EPR?
			return null;
		} else {
			// not an EprAtom 
			// --> check if it occurs in one of the EPR-clauses
			//      if it fulfills the clause, mark the clause as fulfilled
			//      otherwise do nothing, because the literal means nothing to EPR 
			//          --> other theories may report their own conflicts..?
			// (like standard DPLL)
			HashSet<EprNonUnitClause> clauses = mLiteralToClauses.get(literal);
			if (clauses != null)
				for (EprNonUnitClause ec : mLiteralToClauses.get(literal)) {
					ec.setGroundLiteral(literal);
				}

			System.out.println("EPRDEBUG: setLiteral, new fulfilled clauses: " + mStateManager.getFulfilledClauses());
			System.out.println("EPRDEBUG: setLiteral, new not fulfilled clauses: " + mStateManager.getNotFulfilledClauses());

			return null;
		}
	}

	public void setGroundLiteralInClauses(Literal literal) {
		for (EprNonUnitClause ec : mStateManager.getAllClauses())
			ec.setGroundLiteral(literal);
	}

	@Override
	public void backtrackLiteral(Literal literal) {
		System.out.println("EPRDEBUG: backtrackLiteral");
		// .. dual to setLiteral
		
		backtrackEprState(literal);

		// update the fulfillment states of the remaining clauses
		DPLLAtom atom = literal.getAtom();
		if (atom instanceof EprGroundPredicateAtom) {
			// literal is of the form (P x1 .. xn)
			for (EprNonUnitClause ec : mStateManager.getAllClauses())
				ec.unsetGroundLiteral(literal);

		} else if (atom instanceof EprEqualityAtom
				|| atom instanceof EprQuantifiedPredicateAtom) {
			assert false : "DPLLEngine is unsetting a quantified EprAtom --> this cannot be..";
		} else if (atom instanceof CCEquality) {
			CCEquality eq = (CCEquality) atom;
			ApplicationTerm f = (ApplicationTerm) eq.getSMTFormula(mTheory);
			ApplicationTerm lhs = (ApplicationTerm) f.getParameters()[0];
			ApplicationTerm rhs = (ApplicationTerm) f.getParameters()[1];
			
			mEqualityManager.backtrackEquality(lhs, rhs);
		} else {
			// not an EprAtom 
			for (EprNonUnitClause ec : mStateManager.getAllClauses())
				ec.unsetGroundLiteral(literal);

		}
		System.out.println("EPRDEBUG: backtrackLiteral, new fulfilled clauses: " + mStateManager.getFulfilledClauses());
		System.out.println("EPRDEBUG: backtrackLiteral, new not fulfilled clauses: " + mStateManager.getNotFulfilledClauses());
	}

	/**
	 * Pop the EprStateStack, remove the derived clauses from the sets of clauses managed by the theory.
	 * @param literal
	 */
	private void backtrackEprState(Literal literal) {
		mStateManager.endScope(literal);
	}



	@Override
	public Clause checkpoint() {
		System.out.println("EPRDEBUG: checkpoint");
		
		Clause conflict = null;
		
		// have we already a conflict clause in store?
		if (!mStateManager.getConflictClauses().isEmpty()) {
			EprClause realConflict = mStateManager.getConflictClauses().iterator().next();
			System.out.println("EPRDEBUG (checkpoint): found a conflict: " + realConflict);
			//TODO: work on explanation..
			conflict = mStateManager.getDerivedClause(Collections.emptySet(), mTheory, "empty conflict clause");
		} else {
			// try unit propagation
			conflict = eprPropagate();

			if (conflict != null && (conflict instanceof EprClause) &&
					((EprClause) conflict).getQuantifiedPredicateLiterals().length > 0) {
				// the conflict is a proper epr clause --> TODO: ..something about it ..
				assert false : "the conflict is a proper epr clause --> we cannot give it to DPLL as is";
			}
		}
		return conflict;
	}

	/**
	 * Does/queues all propagations that can be made through unit clause ec
	 */
	private Clause eprPropagate() {
		Clause conflict = null;

		HashSet<Clause> notFulfilledCopy = new HashSet<>(mStateManager.getNotFulfilledClauses());
		//unit propagation
		for (Clause c : notFulfilledCopy) {
			EprNonUnitClause ec = (EprNonUnitClause) c;
			EprUnitClause unitLiteral = ec.getUnitClauseLiteral();

			if (unitLiteral != null) {
				System.out.println("EPRDEBUG: found unit clause: " + ec);

				if (unitLiteral instanceof EprGroundUnitClause) {
					Literal groundUnitLiteral = ((EprGroundUnitClause) unitLiteral).getLiteral();
					if (groundUnitLiteral.getAtom() instanceof EprQuantifiedPredicateAtom) {
						assert false : "do we need this case???";
						assert ec.getEqualityAtoms().length == 0;
						EprQuantifiedUnitClause eqlwe = EprHelpers.buildEQLWE(
								groundUnitLiteral,
								//							ec.mExceptedPoints, 
								new EprEqualityAtom[0],
								ec, 
								mTheory, mStateManager);

						conflict = mStateManager.setQuantifiedLiteralWithExceptions(eqlwe);

						if (conflict == null)
							conflict =  setQuantifiedLiteralWEInClauses(eqlwe);
					} else {
						/*
						 * either an EprGroundAtom or a non EprAtom
						 * (plan atm: don't propagate EprEqualities)
						 * --> just propagate the literal through the normal means
						 */
						addAtomToDPLLEngine(groundUnitLiteral.getAtom());
						mPropLitToExplanation.put(groundUnitLiteral, 
								ec.getInstantiationOfClauseForCurrentUnitLiteral());
						mGroundLiteralsToPropagate.add(groundUnitLiteral);
					} 
				} else {
					assert unitLiteral instanceof EprQuantifiedUnitClause;
					conflict = mStateManager.setQuantifiedLiteralWithExceptions(
							(EprQuantifiedUnitClause) unitLiteral);

					if (conflict == null)
						conflict =  setQuantifiedLiteralWEInClauses((EprQuantifiedUnitClause) unitLiteral);
				}
			}
		}
		return conflict;
	}

	public void addAtomToDPLLEngine(DPLLAtom atom) {
		assert !(atom instanceof EprEqualityAtom || atom instanceof EprQuantifiedPredicateAtom);
		if (!mAtomsAddedToDPLLEngine.contains(atom)) { //TODO not so nice, with the extra set..
			mEngine.addAtom(atom);
			mAtomsAddedToDPLLEngine.add(atom);
		}
	}
	

	/**
	 * Apply all the consequences of setting a quantified literal (with exceptions)
	 *  - to all clauses
	 *    this means 
	 *    -- updating the fulfillability state of the literals
	 *    -- adding derived clauses if applicable
	 *       (these might be conflict clauses)
	 *  - to the state of the DPLLEngine
	 *    there may be atoms that interact with the set quantified literal
	 * @param eqlwe
	 * @return
	 */
	public EprClause setQuantifiedLiteralWEInClauses(EprQuantifiedUnitClause eqlwe) {
		EprClause conflict = null;
		/*
		 * propagate a quantified predicate
		 *  --> rules for first-order resolution apply
		 *  --> need to account for excepted points in the corresponding clause
		 */
		// propagate within EprClauses
		//TODO: possibly optimize (so not all clauses have to be treated)
		ArrayList<EprClause> toAdd = new ArrayList<>();
		for (EprNonUnitClause otherEc : mStateManager.getAllClauses()) {
			EprClause conflictClause = otherEc.setQuantifiedLiteral(eqlwe);

			if (conflict == null && conflictClause != null) { // we only return the first conflict we find -- TODO: is that good?..
				// TODO what if the conflict clause is not ground??
				conflict = conflictClause;
			}
		}
		
		// check if there is an Literal in the Engine that conflicts, or is unconstrained. In case propagate.
		for (EprGroundPredicateAtom engineAtom : eqlwe.getPredicateAtom().eprPredicate.getDPLLAtoms()) {
			Literal decideStatus = engineAtom.getDecideStatus();
			
			boolean polaritiesDifferOrUnconstrained = decideStatus == null || 
					(decideStatus.getSign() != eqlwe.getPredicateLiteral().getSign());
			if (polaritiesDifferOrUnconstrained) {

				// is there a unifier?
				TTSubstitution sub = 
						engineAtom.getArgumentsAsTermTuple().match(eqlwe.getPredicateAtom().getArgumentsAsTermTuple(), mEqualityManager);
				if (sub != null) {
					Literal propLit = eqlwe.getPredicateLiteral().getSign() == 1 ? engineAtom : engineAtom.negate();
					mGroundLiteralsToPropagate.add(propLit);
					mPropLitToExplanation.put(propLit, 
							eqlwe.getExplanation().instantiateClause(null, sub));
				}
			}
		}

		return conflict;
	}

	@Override
	public Clause computeConflictClause() {
		System.out.println("EPRDEBUG: computeConflictClause");
		for (Clause c : mStateManager.getNotFulfilledClauses()) {
			EprClause eprClause = (EprClause)	c;
			
			// an epr clause looks like this:
			// x1 =/!= x2 \/ ... \/ xn+1 = c1 ... \/ (P1 ci/xi ... cj/xj) \/ ... \/ (non-EPR literals)
			// we have
			// - (dis)equalities over two quantified variables
			// - equalities over a quantified variable and a constant each
			// - predicates over quantified variables and/or constants
			// - non-epr literals (in mNotFulfilledEprClauses, they are all false (maybe unset??))
			Clause conflict = eprClause.check(mStateManager);
//			checkResult &= conflict == null;
			if (conflict != null)
				return conflict;
		}
		return null;
	}

	@Override
	public Literal getPropagatedLiteral() {
//		System.out.println("EPRDEBUG: getPropagatedLiteral");
		if (!mGroundLiteralsToPropagate.isEmpty()) {
			System.out.println("EPRDEBUG: getPropagatedLiteral propagating: " + mGroundLiteralsToPropagate.getFirst());
		}
		return mGroundLiteralsToPropagate.pollFirst();
	}

	@Override
	public Clause getUnitClause(Literal literal) {
		Clause unitClause = mPropLitToExplanation.get(literal);
		System.out.println("EPRDEBUG: getUnitClause -- returning " + unitClause);
		assert unitClause != null;
		return unitClause;
	}

	@Override
	public Literal getSuggestion() {
		//TODO: think about how to get smart suggestions..
		System.out.println("EPRDEBUG: getSuggestion");
		return null;
	}

	@Override
	public void printStatistics(Logger logger) {
		System.out.println("EPRDEBUG: printStatistics");
	}

	@Override
	public void dumpModel(Logger logger) {
		System.out.println("EPRDEBUG: dumpmodel");
	}

	@Override
	public void increasedDecideLevel(int currentDecideLevel) {
		// TODO Auto-generated method stub
		System.out.println("EPRDEBUG: increasedDecideLevel");

	}

	@Override
	public void decreasedDecideLevel(int currentDecideLevel) {
		// TODO Auto-generated method stub
		System.out.println("EPRDEBUG: decreasedDecideLevel");

	}

	@Override
	public Clause backtrackComplete() {
		// TODO Auto-generated method stub
		System.out.println("EPRDEBUG: backtrackComplete");
		return null;
	}

	@Override
	public void restart(int iteration) {
		// TODO Auto-generated method stub
		System.out.println("EPRDEBUG: restart");

	}

	@Override
	public void removeAtom(DPLLAtom atom) {
		// TODO Auto-generated method stub
		System.out.println("EPRDEBUG: removeAtom" + atom);

	}

	@Override
	public Object push() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void pop(Object object, int targetlevel) {
		// TODO Auto-generated method stub

	}

	@Override
	public Object[] getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void fillInModel(Model model, Theory t, SharedTermEvaluator ste) {
		// TODO Auto-generated method stub

	}
	/**
	 * Add an EprClause for a given a non-ground set of literals.
	 * 
	 * Speciality: apply destructive equality reasoning (DER)
	 *  If the clause becomes ground through DER, don't add it as an EprClause, but return the corresponding literals
	 *   instead (in order to be added as a DPLL clause).
	 *  Otherwise return null
	 * 
	 * @param lits literals where at least one variable is free (thus implicitly forall-quantified)
	 * @param hook
	 * @param proof
	 * @return equivalent ground set of literals if DER obtained one, null otherwise
	 */
	public Literal[] addEprClause(Literal[] lits, ClauseDeletionHook hook, ProofNode proof) {
		
		ApplyDestructiveEqualityReasioning ader = new ApplyDestructiveEqualityReasioning(lits);
		
		if (ader.isResultGround()) {
			return ader.getResult().toArray(new Literal[ader.getResult().size()]);
		} 
		
		HashSet<Literal> literals = ader.getResult();
		
		//TODO: do something about hook and proof..
		EprNonUnitClause newEprClause = mStateManager.getBaseClause(literals, mTheory);
		mConflict |= mStateManager.addBaseClause(newEprClause);
	
		for (Literal li : lits) {
			updateLiteralToClauses(li, newEprClause);
		}
		
		return null;
	}

	void updateLiteralToClauses(Literal lit, EprNonUnitClause c) {
		HashSet<EprNonUnitClause> clauses = mLiteralToClauses.get(lit);
		if (clauses == null) {
			clauses = new HashSet<EprNonUnitClause>();
			mLiteralToClauses.put(lit, clauses);
		}
		clauses.add(c);
	}

	/**
	 * A term is an EPR atom, if it is
	 *  - an atom
	 *  - contains free Termvariables (i.e. implicitly quantified variables)
	 *  - an ApplicationTerm with function symbol either "=" or an uninterpreted predicate
	 *  further checks:
	 *  - may not contain function symbols
	 */
	public static boolean isQuantifiedEprAtom(Term idx) {
		if (idx.getFreeVars().length > 0) {
			if (idx instanceof ApplicationTerm) {
				if (isEprPredicate(((ApplicationTerm) idx).getFunction())) return true;
				if ((((ApplicationTerm) idx).getFunction()).getName().equals("=")) return true;
			}
		}
		return false;
	}

	private static boolean isEprPredicate(FunctionSymbol function) {
		//TODO: we should collect all the predicates that are managed by EPR --> implement a check accordingly, here
		if (function.getName().equals("not")) return false;
		if (function.getName().equals("or")) return false;
		return true;
	}
	
	public Set<Clause> getFulfilledClauses() {
		HashSet<Clause> cls = new HashSet<>();
		cls.addAll(mStateManager.getFulfilledClauses());
		return cls;
	}

	public Set<Clause> getNotFulfilledClauses() {
		HashSet<Clause> cls = new HashSet<>();
		cls.addAll(mStateManager.getNotFulfilledClauses());
		return cls;
	}

	public EprAtom getEprAtom(ApplicationTerm idx, int hash, int assertionStackLevel, Object mCollector) {
		if (idx.getFunction().getName().equals("=")) {
			assert idx.getFreeVars().length > 0;
		    ApplicationTerm subTerm = applyAlphaRenaming(idx, mCollector);
			return new EprEqualityAtom(subTerm, hash, assertionStackLevel);
		} else {
			EprPredicate pred = mFunctionSymbolToEprPredicate.get(idx.getFunction());
			if (pred == null) {
				pred = new EprPredicate(idx.getFunction(), idx.getParameters().length);
				mFunctionSymbolToEprPredicate.put(idx.getFunction(), pred);
				mStateManager.addNewEprPredicate(pred);
			}
			if (idx.getFreeVars().length == 0) {
				EprGroundPredicateAtom egpa = pred.getAtomForPoint(new TermTuple(idx.getParameters()), 
						mTheory, 
						mEngine.getAssertionStackLevel());
				pred.addDPLLAtom(egpa);
				return egpa;
			} else {
				ApplicationTerm substitutedTerm = applyAlphaRenaming(idx, mCollector);
//				return new EprQuantifiedPredicateAtom(substitutedTerm, hash, assertionStackLevel, pred);
				return pred.getAtomForTermTuple(new TermTuple(substitutedTerm.getParameters()), mTheory, assertionStackLevel);
			}
		}
	}

	private ApplicationTerm applyAlphaRenaming(ApplicationTerm idx, Object mCollector) {
		TermTuple tt = new TermTuple(idx.getParameters());

		HashMap<TermVariable, Term> sub;
		// mCollector is a BuildClause-Object 
		// --> we need to apply the same substitution in every literal of the clause..
		if (mCollector != null) {
			sub = mBuildClauseToAlphaRenamingSub.get(mCollector);
		} else {
			// if mCollector is null, this means we are in a unit clause (i think...), 
			// and we can just use a fresh substitution
			sub = new HashMap<>();
		}

		for (TermVariable fv : idx.getFreeVars()) {
			if (sub.containsKey(fv))
				continue;
			sub.put(fv, mTheory.createFreshTermVariable(fv.getName(), fv.getSort()));
		}
		TermTuple ttSub = tt.applySubstitution(sub);
		ApplicationTerm subTerm = mTheory.term(idx.getFunction(), ttSub.terms);
		return subTerm;
	}

	public void notifyAboutNewClause(Object buildClause) {
		mBuildClauseToAlphaRenamingSub.put(buildClause, new HashMap<TermVariable, Term>());
	}
	
	/**
	 * Apply destructive equality reasoning to the clause consisting of the given
	 * literals.
	 * Procedure:
	 *  - build one big substitution which has one entry for each equality
	 *  - apply the subtitution to each (quantified) literal in the clause
	 *   (it may be a bit suprising that this works, but I think it does,
	 *    example: {x != c, x != d, P(x)} will yield the substitution [x <- c, x <- d], which
	 *           will yield the clause {c != c, c != d, P(c)} which seems right.) //TODO: make sure..
	 */
	class ApplyDestructiveEqualityReasioning {

		HashSet<Literal> mResult;
		boolean mIsResultGround = true;
		
		public ApplyDestructiveEqualityReasioning(Literal[] literals) {
			applyDER(new HashSet<Literal>(Arrays.asList(literals)));
		}
		
		private void applyDER(HashSet<Literal> literals) {
			HashSet<Literal> currentClause = literals;
			Literal disEquality = findDisequality(literals);
			mResult = new HashSet<>(literals);
			mIsResultGround = false;
			while (disEquality != null) {
				currentClause.remove(disEquality);

				TTSubstitution sub = extractSubstitutionFromEquality((EprEqualityAtom) disEquality.getAtom());			

				mResult = new HashSet<>();
				mIsResultGround = true;
				for (Literal l : currentClause) {
					Literal sl = getSubstitutedLiteral(sub, l);
					if (sl.getAtom() instanceof TrueAtom) {
						if (sl.getSign() == 1) {
							// do nothing (tautology will be detected later)
						} else {
							continue; //omit "false"
						}
					} else if (sl.getAtom() instanceof EprEqualityAtom ||
							sl.getAtom() instanceof EprQuantifiedPredicateAtom) {
						mIsResultGround = false;
					} else if (sl.getAtom() instanceof EprGroundPredicateAtom ||
							sl.getAtom() instanceof CCEquality) {
						addAtomToDPLLEngine(sl.getAtom());
					}
					mResult.add(sl);
				}
				currentClause = mResult;

				disEquality = findDisequality(currentClause);
			}
		}

		public TTSubstitution extractSubstitutionFromEquality(EprEqualityAtom eea) {
			TermTuple tt = eea.getArgumentsAsTermTuple();
			TermVariable tv = null;
			Term t = null;
			if (tt.terms[0] instanceof TermVariable) {
				tv = (TermVariable) tt.terms[0];
				t = tt.terms[1];
			} else {
				tv = (TermVariable) tt.terms[1];
				t = tt.terms[0];
			}
			return new TTSubstitution(tv, t);
		}

		private Literal findDisequality(HashSet<Literal> literals) {
			for (Literal l : literals) {
				if (l.getSign() != 1 && l.getAtom() instanceof EprEqualityAtom)
					return l;
			}
			return null;
		}

		/**
		 * Applies sub to li and adds the resulting Literal to newLits.
		 * Also updates mIsResultGround (i.e. when a Literal remains non-ground, it is set to false)
		 * @param sub substitution to be applied
		 * @param newLits set to add to
		 * @param li literal whose variables should be substituted
		 */
		public Literal getSubstitutedLiteral(TTSubstitution sub, Literal li) {
			if (li.getAtom() instanceof EprQuantifiedPredicateAtom 
					|| li.getAtom() instanceof EprEqualityAtom) {
				boolean liPositive = li.getSign() == 1;
				TermTuple liTT = ((EprAtom) li.getAtom()).getArgumentsAsTermTuple();

				TermTuple newTT = sub.apply(liTT);

				if (newTT.equals(liTT)) {
					return li;
				}

				if (li.getAtom() instanceof EprEqualityAtom) {
					if (newTT.isGround()) {
						if (newTT.terms[0] == newTT.terms[1] && liPositive) {
							return new DPLLAtom.TrueAtom();
						} else if (newTT.terms[0] == newTT.terms[1] && !liPositive) {
							return new DPLLAtom.TrueAtom().negate();
						}
						throw new UnsupportedOperationException();// how to obtain a fresh CCEquality???
//							addAtomToDPLLEngine(ea);
					} else {
						EprEqualityAtom eea = new EprEqualityAtom(mTheory.term("=", newTT.terms),
								0,  //TODO use good hash
								li.getAtom().getAssertionStackLevel());
						return liPositive ? eea : eea.negate();
					}
				} else {
					// li.getAtom() is an EprQuantifiedPredicateAtom
					EprPredicate liPred = ((EprQuantifiedPredicateAtom) li.getAtom()).eprPredicate;

					EprAtom ea = null;
					if (newTT.isGround()) {
						ea = liPred.getAtomForPoint(newTT, mTheory, li.getAtom().getAssertionStackLevel());
					} else {
						ea = liPred.getAtomForTermTuple(newTT, mTheory, li.getAtom().getAssertionStackLevel());
					}
					return liPositive ? ea : ea.negate();
				}
			} else {
				return li;
			}
		}

		public HashSet<Literal> getResult() {
			return mResult;
		}

		public boolean isResultGround() {
			return mIsResultGround;
		}
		
		
	}
}
