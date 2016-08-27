package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom.TrueAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprClauseOld;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprGroundUnitClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprNonUnitClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprQuantifiedUnitClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprUnitClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.EprStateManager;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashSet;

public class EprTheory implements ITheory {

	HashMap<FunctionSymbol, EprPredicate> mFunctionSymbolToEprPredicate = new HashMap<FunctionSymbol, EprPredicate>();

	ArrayDeque<Literal> mGroundLiteralsToPropagate = new ArrayDeque<Literal>();


	HashMap<Object, HashMap<TermVariable, Term>> mBuildClauseToAlphaRenamingSub = 
			new HashMap<Object, HashMap<TermVariable,Term>>();

	/**
	 * if we propagate a ground literal we have to be able to give a unit clause
	 * that explains the literal
	 */
	private HashMap<Literal, Clause> mPropLitToExplanation = new HashMap<Literal, Clause>();

	ScopedHashSet<DPLLAtom> mAtomsAddedToDPLLEngine = new ScopedHashSet<DPLLAtom>();
	
	EqualityManager mEqualityManager;

	/**
	 * If this is set to true, EprTheory just computes all groundings for a given quantified clause
	 * and returns them to the DPLLEngine.
	 */
	private final boolean mGroundAllMode;
	private ArrayList<Literal[]> mAllGroundingsOfLastAddedEprClause;

	private EprStateManager mStateManager;
	private DawgFactory<ApplicationTerm, TermVariable> mDawgFactory;

	private CClosure mCClosure;
	private Clausifier mClausifier;
	private LogProxy mLogger;
	private Theory mTheory;
	private DPLLEngine mEngine;


	public EprTheory(Theory th, DPLLEngine engine, CClosure cClosure, Clausifier clausifier, boolean solveThroughGrounding) {
		mTheory = th;
		mEngine = engine;
		mClausifier = clausifier;

		mEqualityManager = new EqualityManager();
		mStateManager = new EprStateManager(this);
		mGroundAllMode = solveThroughGrounding;
		
		mDawgFactory = new DawgFactory<ApplicationTerm,TermVariable>(mStateManager.getAllConstants(), this);

		mLogger = clausifier.getLogger();
	}

	@Override
	public Clause startCheck() {
		mLogger.debug("EPRDEBUG: startCheck");
		return null;
	}

	@Override
	public void endCheck() {
		mLogger.debug("EPRDEBUG: endCheck");
	}

	@Override
	public Clause setLiteral(Literal literal) {
		if (mGroundAllMode)
			return null;
		mLogger.debug("EPRDEBUG: setLiteral " + literal);
		
		DPLLAtom atom = literal.getAtom();
		
		if (atom instanceof EprGroundPredicateAtom) {
			// literal is of the form (P c1 .. cn) (no quantification, but an EprPredicate)
			// is being set by the DPLLEngine (the quantified EprPredicateAtoms are not known to the DPLLEngine)

			/* plan:
			 * 
			 * The unquantified epr literal gets a DecideStackLiteral on the Epr
			 * decide stack.
			 * (it is on two decide stacks then - the one from the DPLLEngine 
			 *  and the one in EprStateManager)
			 */

			Clause conflict = mStateManager.setEprGroundLiteral(literal);
			if (conflict != null)
				return conflict; // then act as if the literal is not set, right?

		} else if (atom instanceof EprQuantifiedEqualityAtom 
				|| atom instanceof EprQuantifiedPredicateAtom) {

			assert false : "DPLLEngine is setting a quantified EprAtom --> this cannot be..";

		} else if (atom instanceof CCEquality) {
			if (literal.getSign() == 1) {
				CCEquality eq = (CCEquality) atom;
				
				return mStateManager.setGroundEquality((CCEquality) atom);
			}

			// TODO do ground disequalities have an impact for EPR?

			mStateManager.updateClausesOnSetDpllLiteral(literal);
		} else {
			// neither an EprAtom nor an Equality

			mStateManager.updateClausesOnSetDpllLiteral(literal);
	
		}

		mLogger.debug("EPRDEBUG: setLiteral, new fulfilled clauses: " 
				+ mStateManager.getFulfilledClauses());
		mLogger.debug("EPRDEBUG: setLiteral, new not fulfilled clauses: " 
				+ mStateManager.getNotFulfilledClauses());

		return null;
	}

	@Override
	public void backtrackLiteral(Literal literal) {
		if (mGroundAllMode)
			return;
		mLogger.debug("EPRDEBUG: backtrackLiteral");

		// .. dual to setLiteral
		
		// update the fulfillment states of the remaining clauses
		DPLLAtom atom = literal.getAtom();
		if (atom instanceof EprGroundPredicateAtom) {
			// literal is of the form (P x1 .. xn)

			mStateManager.unsetEprGroundLiteral(literal);

		} else if (atom instanceof EprQuantifiedEqualityAtom
				|| atom instanceof EprQuantifiedPredicateAtom) {

			assert false : "DPLLEngine is unsetting a quantified EprAtom --> this cannot be..";

		} else if (atom instanceof CCEquality) {
			assert atom.getSign() == literal.getSign() : "TODO: treat backtracking of disequality";
			mStateManager.unsetGroundEquality((CCEquality) atom);
			
		} else {
			// neither an EprAtom nor an equality

			mStateManager.updateClausesOnBacktrackDpllLiteral(literal);

		}
		mLogger.debug("EPRDEBUG: backtrackLiteral, new fulfilled clauses: " + mStateManager.getFulfilledClauses());
		mLogger.debug("EPRDEBUG: backtrackLiteral, new not fulfilled clauses: " + mStateManager.getNotFulfilledClauses());
	}

	@Override
	public Clause checkpoint() {
		if (mGroundAllMode)
			return null;
		mLogger.debug("EPRDEBUG: checkpoint");
		
		Clause conflict = null;
		
//		// have we already a conflict clause in store?
//		if (!mStateManager.getConflictClauses().isEmpty()) {
//			EprClauseOld realConflict = mStateManager.getConflictClauses().iterator().next();
//			mLogger.debug("EPRDEBUG (checkpoint): found a conflict: " + realConflict);
//			//TODO: work on explanation..
//			conflict = mStateManager.getDerivedClause(new HashSet<Literal>(0), 
//					this, "empty conflict clause");
//		} else {
//			// try unit propagation
//			conflict = eprPropagate();
//
//			if (conflict != null && (conflict instanceof EprClauseOld) &&
//					((EprClauseOld) conflict).getQuantifiedPredicateLiterals().length > 0) {
//				// the conflict is a proper epr clause --> TODO: ..something about it ..
//				assert false : "the conflict is a proper epr clause --> we cannot give it to DPLL as is";
//			}
//		}

		return conflict;
	}

	@Override
	public Clause computeConflictClause() {
		if (mGroundAllMode)
			return null;
		mLogger.debug("EPRDEBUG: computeConflictClause");
		
		/*
		 * plan:
		 *  (assuming that the internal epr model is consistent at this point)
		 *  1 check if current model is complete
		 *    if yes: return sat
		 *    if no:
		 *  2 set a EprQuantifiedUnitClause that makes it more complete
		 *     is there a conflict now?
		 *    if yes:
		 *     analyze the conflict and do one of the following
		 *      - set a different EprQuantifiedUnitClause (for example with added exceptions)
		 *      - return a ground conflict clause
		 *    if no:
		 *     goto 1
		 */
		
//		for (EprClause ec : mStateManager.getAllEprClauses()) {
//			Clause conflict = ec.getConflict();
//			if (conflict != null) {
//				return conflict;
//			}
//		}


		
		return mStateManager.eprDpllLoop();
	}

	@Override
	public Literal getPropagatedLiteral() {
		if (!mGroundLiteralsToPropagate.isEmpty()) {
			mLogger.debug("EPRDEBUG: getPropagatedLiteral propagating: " + mGroundLiteralsToPropagate.getFirst());
			return mGroundLiteralsToPropagate.pollFirst();
		}
		return null;
	}

	@Override
	public Clause getUnitClause(Literal literal) {
		Clause unitClause = mPropLitToExplanation.get(literal);
		mLogger.debug("EPRDEBUG: getUnitClause -- returning " + unitClause);
		assert unitClause != null;
		return unitClause;
	}

	@Override
	public Literal getSuggestion() {
		if (mGroundAllMode)
			return null;
		//TODO: think about how to get smart suggestions..
		mLogger.debug("EPRDEBUG: getSuggestion");
		return null;
	}

	@Override
	public void increasedDecideLevel(int currentDecideLevel) {
		if (mGroundAllMode)
			return;
		// TODO Auto-generated method stub
		mLogger.debug("EPRDEBUG: increasedDecideLevel");

	}

	@Override
	public void decreasedDecideLevel(int currentDecideLevel) {
		if (mGroundAllMode)
			return;
		// TODO Auto-generated method stub
		mLogger.debug("EPRDEBUG: decreasedDecideLevel");

	}

	@Override
	public Clause backtrackComplete() {
		// TODO Auto-generated method stub
		mLogger.info("EPRDEBUG: backtrackComplete");
		return null;
	}

	@Override
	public void restart(int iteration) {
		// TODO Auto-generated method stub
		mLogger.info("EPRDEBUG: restart");

	}

	@Override
	public void removeAtom(DPLLAtom atom) {
		if (mGroundAllMode)
			return;
		// TODO Auto-generated method stub
		mLogger.debug("EPRDEBUG: removeAtom" + atom);
	}

	@Override
	public Object push() {
//		mStateManager.beginScope("push");
		mStateManager.push();
		mAtomsAddedToDPLLEngine.beginScope();
		return null;
	}

	@Override
	public void pop(Object object, int targetlevel) {
//		mStateManager.endScope("push");
		for (int i = mClausifier.getStackLevel(); i > targetlevel; i--)
			mStateManager.pop();
		mAtomsAddedToDPLLEngine.endScope();
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
	public void addAtomToDPLLEngine(DPLLAtom atom) {
		assert !(atom instanceof EprQuantifiedEqualityAtom || atom instanceof EprQuantifiedPredicateAtom);
		if (atom instanceof CCEquality)
			return; //added to engine at creation, right?..
		if (!mAtomsAddedToDPLLEngine.contains(atom)) { //TODO not so nice, with the extra set..
			mEngine.addAtom(atom);
			mAtomsAddedToDPLLEngine.add(atom);
		}
	}

	/**
	 * Add an EprClause for a given a non-ground set of literals.
	 * 
	 * Specialty: apply destructive equality reasoning (DER)
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
		//TODO: do something about hook and proof..
		
		// we need to track all constants for grounding mode (and other applications??)
		this.addConstants(EprHelpers.collectAppearingConstants(lits, mTheory));

		
		// we remove disequalities occuring in the clause through destructive equality reasoning
		// if the clause is ground afterwards, we just give it back to, the DPLLEngine
		// otherwise we add it as an EprClause
		ApplyDestructiveEqualityReasoning ader = new ApplyDestructiveEqualityReasoning(lits);
		if (ader.isResultGround()) {
			return ader.getResult().toArray(new Literal[ader.getResult().size()]);
		} 
		HashSet<Literal> literals = ader.getResult();
		
		mStateManager.addClause(literals);
		
		return null;
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
				if (isEprPredicate(((ApplicationTerm) idx).getFunction())) 
					return true;
				if ((((ApplicationTerm) idx).getFunction()).getName().equals("=")
						&& !(((ApplicationTerm) idx).getParameters()[0].getSort().getName().equals("Bool")))
					return true;
			}
		}
		return false;
	}

	private static boolean isEprPredicate(FunctionSymbol function) {
		if (function.getName().equals("not")) 
			return false;
		if (function.getName().equals("or")) 
			return false;
		if (function.getName().equals("and")) 
			return false;
		if (function.getName().equals("let")) 
			return false;
		if (function.getName().equals("ite")) 
			return false;
		if (function.getName().equals("=")) 
			return false;
		return true;
	}
	
	public Set<Clause> getFulfilledClauses() {
		HashSet<Clause> cls = new HashSet<Clause>();
		cls.addAll(mStateManager.getFulfilledClauses());
		return cls;
	}

	public Set<Clause> getNotFulfilledClauses() {
		HashSet<Clause> cls = new HashSet<Clause>();
		cls.addAll(mStateManager.getNotFulfilledClauses());
		return cls;
	}

	public EprAtom getEprAtom(ApplicationTerm idx, int hash, int assertionStackLevel, Object mCollector) {
		if (idx.getFunction().getName().equals("=")) {
			assert idx.getFreeVars().length > 0;
		    ApplicationTerm subTerm = applyAlphaRenaming(idx, mCollector);
			return new EprQuantifiedEqualityAtom(subTerm, hash, assertionStackLevel);
		} else {
			EprPredicate pred = mFunctionSymbolToEprPredicate.get(idx.getFunction());
			if (pred == null) {
				pred = new EprPredicate(idx.getFunction(), idx.getParameters().length, this);
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
				return pred.getAtomForTermTuple(
						new TermTuple(substitutedTerm.getParameters()), 
						mTheory, 
						assertionStackLevel);
			}
		}
	}

	private ApplicationTerm applyAlphaRenaming(ApplicationTerm idx, Object mCollector) {
		boolean cutShort = true;
		if (cutShort)
			return idx;
		
		TermTuple tt = new TermTuple(idx.getParameters());

		HashMap<TermVariable, Term> sub;
		// mCollector is a BuildClause-Object 
		// --> we need to apply the same substitution in every literal of the clause..
		if (mCollector != null) {
			sub = mBuildClauseToAlphaRenamingSub.get(mCollector);
		} else {
			// if mCollector is null, this means we are in a unit clause (i think...), 
			// and we can just use a fresh substitution
			sub = new HashMap<TermVariable, Term>();
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
	 * Used for tracking all constants that appear in any clause that is currently asserted.
	 * @param constants
	 */
	public void addConstants(HashSet<ApplicationTerm> constants) {
		mStateManager.addConstants(constants);
	}

	public ArrayList<Literal[]> getAllGroundingsOfLastAddedEprClause() {
		return mAllGroundingsOfLastAddedEprClause;
	}

	public Theory getTheory() {
		return mTheory;
	}
	
	public CClosure getCClosure() {
		return mCClosure;
	}
	
	public EprStateManager getStateManager() {
		return mStateManager;
	}
	
	public DawgFactory<ApplicationTerm, TermVariable> getDawgFactory() {
		return mDawgFactory;
	}
	
	public EqualityManager getEqualityManager() {
		return mEqualityManager;
	}
	
	public Clausifier getClausifier() {
		return mClausifier;
	}
	
	public boolean isGroundAllMode() {
		return mGroundAllMode;
	}

	/**
	 * This is called whenever the Clausifier introduces a new constant term.
	 * (The only case I can think of now is at skolemization..,
	 *  but if we want constants handling on-the-fly, we may use this elsewhere, too..)
	 *  --> in groundAll-mode adding a constant means adding further instantiations of the 
	 *    EprClauses
	 * @param skolems
	 * @return 
	 */
	public void addSkolemConstants(Term[] skolems) {

		HashSet<ApplicationTerm> constants = new HashSet<ApplicationTerm>();
		for (Term t : skolems)
			constants.add((ApplicationTerm) t);
		
		mStateManager.addConstants(constants);
	}

	public LogProxy getLogger() {
		return mLogger;
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
	class ApplyDestructiveEqualityReasoning {

		HashSet<Literal> mResult;
		boolean mIsResultGround = true;

		public ApplyDestructiveEqualityReasoning(Literal[] literals) {
			applyDER(new HashSet<Literal>(Arrays.asList(literals)));
		}

		private void applyDER(HashSet<Literal> literals) {
			HashSet<Literal> currentClause = new HashSet<Literal>(literals);
			Literal disEquality = findDisequality(currentClause);
			mResult = currentClause;
			mIsResultGround = false;
			while (disEquality != null) {
				currentClause.remove(disEquality);

				TTSubstitution sub = extractSubstitutionFromEquality((EprQuantifiedEqualityAtom) disEquality.getAtom());			

				mResult = new HashSet<Literal>();
				mIsResultGround = true;
				for (Literal l : currentClause) {
					//						Literal sl = getSubstitutedLiteral(sub, l);
					Literal sl = EprHelpers.applySubstitution(sub, l, EprTheory.this, true);
					if (sl.getAtom() instanceof TrueAtom) {
						if (sl.getSign() == 1) {
							// do nothing/just add it to the result (tautology will be detected later)
						} else {
							continue; //omit "false"
						}
					} else if (sl.getAtom() instanceof EprQuantifiedEqualityAtom ||
							sl.getAtom() instanceof EprQuantifiedPredicateAtom) {
						mIsResultGround = false;
					} else if (sl.getAtom() instanceof EprGroundPredicateAtom ||
							sl.getAtom() instanceof CCEquality) {
						addAtomToDPLLEngine(sl.getAtom());
					} else if (sl.getAtom() instanceof NamedAtom) {
						// do nothing/just add it to the result
					} else
						assert false : "case not forseen..";
					mResult.add(sl);
				}
				currentClause = mResult;

				disEquality = findDisequality(currentClause);
			}
		}

		public TTSubstitution extractSubstitutionFromEquality(EprQuantifiedEqualityAtom eea) {
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
				if (l.getSign() != 1 && l.getAtom() instanceof EprQuantifiedEqualityAtom)
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
					|| li.getAtom() instanceof EprQuantifiedEqualityAtom) {
				boolean liPositive = li.getSign() == 1;
				TermTuple liTT = ((EprAtom) li.getAtom()).getArgumentsAsTermTuple();

				TermTuple newTT = sub.apply(liTT);

				if (newTT.equals(liTT)) {
					return li;
				}

				if (li.getAtom() instanceof EprQuantifiedEqualityAtom) {
					if (newTT.isGround()) {
						if (newTT.terms[0] == newTT.terms[1] && liPositive) {
							return new DPLLAtom.TrueAtom();
						} else if (newTT.terms[0] == newTT.terms[1] && !liPositive) {
							return new DPLLAtom.TrueAtom().negate();
						}
						throw new UnsupportedOperationException();// how to obtain a fresh CCEquality???
						//							addAtomToDPLLEngine(ea);
					} else {
						EprQuantifiedEqualityAtom eea = new EprQuantifiedEqualityAtom(mTheory.term("=", newTT.terms),
								0,  //TODO use good hash
								li.getAtom().getAssertionStackLevel());
						return liPositive ? eea : eea.negate();
					}
				} else {
					// li.getAtom() is an EprQuantifiedPredicateAtom
					EprPredicate liPred = ((EprQuantifiedPredicateAtom) li.getAtom()).getEprPredicate();

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
	
	/////////////////////////////////////// old stuff (may be reusable) //////////////////////////////

	/**
	 * Does/queues all propagations that can be made through unit clause ec
	 */
	@Deprecated
	private Clause eprPropagate() {
		Clause conflict = null;
	
		HashSet<Clause> notFulfilledCopy = new HashSet<Clause>(
				mStateManager.getNotFulfilledClauses());
		//unit propagation
		for (Clause c : notFulfilledCopy) {
			EprNonUnitClause ec = (EprNonUnitClause) c;
			EprUnitClause unitLiteral = ec.getUnitClauseLiteral();
	
			if (unitLiteral != null) {
				mLogger.debug("EPRDEBUG: found unit clause: " + ec);
	
				if (unitLiteral instanceof EprGroundUnitClause) {
					Literal groundUnitLiteral = ((EprGroundUnitClause) unitLiteral).getPredicateLiteral();
					if (groundUnitLiteral.getAtom() instanceof EprQuantifiedPredicateAtom) {
						assert false : "do we need this case???";
						assert ec.getEqualityAtoms().length == 0;
						EprQuantifiedUnitClause eqlwe = EprHelpers.buildEQLWE(
								groundUnitLiteral,
								//							ec.mExceptedPoints, 
								new EprQuantifiedEqualityAtom[0],
								ec, 
								this);
	
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
								ec.getInstantiationOfClauseForCurrentUnitLiteral(unitLiteral));
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
	@Deprecated
	public EprClauseOld setQuantifiedLiteralWEInClauses(EprQuantifiedUnitClause eqlwe) {
		EprClauseOld conflict = null;
		/*
		 * propagate a quantified predicate
		 *  --> rules for first-order resolution apply
		 *  --> need to account for excepted points in the corresponding clause
		 */
		// propagate within EprClauses
		//TODO: possibly optimize (so not all clauses have to be treated)
		ArrayList<EprClauseOld> toAdd = new ArrayList<EprClauseOld>();
		for (EprNonUnitClause otherEc : mStateManager.getAllClauses()) {
			EprClauseOld conflictClause = otherEc.setQuantifiedLiteral(eqlwe);

			if (conflict == null && conflictClause != null) { // we only return the first conflict we find -- TODO: is that good?..
				// TODO what if the conflict clause is not ground??
				conflict = conflictClause;
			}
		}
		
		// check if there is an Literal in the Engine that conflicts, or is unconstrained. In case propagate.
		for (EprGroundPredicateAtom engineAtom : eqlwe.getPredicateAtom().getEprPredicate().getDPLLAtoms()) {
			Literal decideStatus = engineAtom.getDecideStatus();
			
			boolean polaritiesDifferOrUnconstrained = decideStatus == null || 
					(decideStatus.getSign() != eqlwe.getPredicateLiteral().getSign());
			if (polaritiesDifferOrUnconstrained) {

				// is there a unifier?
				TTSubstitution sub = 
						engineAtom.getArgumentsAsTermTuple()
						.match(eqlwe.getPredicateAtom().getArgumentsAsTermTuple(), mEqualityManager);
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

	/**
	 * Pop the EprStateStack, remove the derived clauses from the sets of clauses managed by the theory.
	 * @param literal
	 */
	@Deprecated
	private void backtrackEprState(Literal literal) {
		mStateManager.endScope(literal);
	}

	@Deprecated
	private void setGroundLiteralInClauses(Literal literal) {
		for (EprNonUnitClause ec : mStateManager.getAllClauses())
			ec.setGroundLiteral(literal);
	}

	/**
		 * 
		 * @return an EprPredicate whose model is not complete in the current state, null if there is none.
		 */
	@Deprecated
	private EprPredicate isEprModelComplete() {

		//		for (EprPredicate pred : mStateManager.getAllEprPredicates()) {//careful: changed the return type of getAll.. to _Scoped_HashSet..
		//			int arity = pred.arity;
		//			
		//			assert arity <= 2;
		//
		//			if (arity == 2) {
		//				ArrayList<EprQuantifiedUnitClause> setQuantifiedLiterals = 
		//						mStateManager.getSetLiterals(pred);
		//				
		//				HashMap<TermVariable, ApplicationTerm> missingPointSets
		//					= new HashMap<TermVariable, ApplicationTerm>();
		//				
		//				HashMap<ApplicationTerm, ApplicationTerm> missingPoints
		//				 	= new HashMap<ApplicationTerm, ApplicationTerm>();
		//				
		//				boolean reflexivePointsCovered = false;
		//				
		//				boolean nonReflexivePointsCovered = false;
		//
		//				for (EprQuantifiedUnitClause setQLit : setQuantifiedLiterals) {
		//					TermTuple tt = setQLit.getPredicateAtom().getArgumentsAsTermTuple();
		////					if (tt.getFreeVars().size() == arity 
		////							&& setQLit.getEqualityAtoms().length == 0) {
		////						// this EprPredicate is covered
		////					}
		//					if (tt.terms[0] instanceof TermVariable
		//							&& tt.terms[0] == tt.terms[1]) {
		//						reflexivePointsCovered = true;
		//
		//					} else if (tt.terms[0] instanceof TermVariable
		//							&& tt.terms[1] instanceof TermVariable
		//							&& tt.terms[0] != tt.terms[1]) {
		//
		//					}
		//
		//
		//				}
		//			} else if (arity == 1) {
		//				
		//			}
		//
		//		}
		return null;
	}

	/**
	 * Assumes that the model of pred is incomplete (i.e., the current state assigns no
	 * truth value to at least one point).
	 * Returns a EprUnitClause that does not contradict the current model, and that, 
	 * when set, extends the current model by at least one point.
	 * (There might be a lot of heuristics going on here..)
	 * @param pred An EprPredicate whose model is currently incomplete
	 * @return an EprUnitClause that, when set, (partially) completes the model of pred
	 */
	@Deprecated
	private EprUnitClause getCompletingClause(EprPredicate pred) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * Called by computeConflictClause().
	 * Checks if the current model for the epr predicates is complete 
	 * (i.e. every predicate has a value for every point in it)
	 * If it is complete (and consistent), returns null (meaning no conflict)
	 * If the model is not complete, this sets (and possibly backtracks) EprUnitClauses
	 * until the model is complete, or a ground conflict has been derived.
	 * In the latter case, the ground conflict is returned.
	 * @return
	 */
	@Deprecated
	private Clause completeModel() {
		EprPredicate pred = isEprModelComplete();
		while (pred != null) {
			//TODO implement!
			EprUnitClause completingClause  = getCompletingClause(pred);
			
			//TODO maybe unite these two methods..
			//TODO insert "decide point"
			if (completingClause instanceof EprQuantifiedUnitClause)
				setQuantifiedLiteralWEInClauses((EprQuantifiedUnitClause) completingClause);
			else
				setGroundLiteralInClauses(completingClause.getPredicateLiteral());
	
	
			pred = isEprModelComplete();
		}
		return null;
	}

	@Override
	public void printStatistics(LogProxy logger) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void dumpModel(LogProxy logger) {
		// TODO Auto-generated method stub
		
	}

}
