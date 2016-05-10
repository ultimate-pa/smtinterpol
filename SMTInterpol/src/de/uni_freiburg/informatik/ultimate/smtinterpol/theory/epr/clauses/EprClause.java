package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom.TrueAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprStateManager;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EqualityManager;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution.SubsPair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution.TPair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;

/**
 * Represents a clause that contains free variables, i.e., that is implicitly universally quantified.
 *  
 * Specialities:
 *  The literals in an EprClause are of three kinds
 *  - nonEprLiterals 
 *    Literals as normal, don't contain quantified variables, are set by the DPLLEngine
 *  - quantified equalities
 *    they essentially represent exceptions to the quantified EprLiterals
 *  - not quantified EprPredicateLiterals 
 *  - quantified EprPredicateLiterals 
 *    implicitly quantified literals those have special states of fulfillability
 *    -- not fulfilled
 *       this is the case if at least one point (that is not excepted by an equality) is set conversely to the literal
 *    -- fulfillable
 *       if there is no counterexample (point) to the literal in the current state
 *    -- fulfilled
 *       if, e.g. through unit propagation, all points concerned by the quantified predicate are set the right way
 */
public abstract class EprClause extends Clause {
	
	protected final boolean isFreshAlphaRenamed;
	protected final TTSubstitution mFreshAlphaRenaming;

	
	enum FulfillabilityStatus { Fulfilled, Fulfillable, Unfulfillable };

	protected EprQuantifiedEqualityAtom[] eprQuantifiedEqualityAtoms;
	protected Literal[] eprQuantifiedPredicateLiterals;
	protected Literal[] groundLiterals;
	
	/**
	 * used for
	 *  - debugging
	 *  - finding tautologies
	 */
	HashSet<Literal> mAllLiterals = new HashSet<>();
	
	HashSet<TermVariable> mFreeVars = new HashSet<>();
	
	private boolean isTautology = false;

	protected Theory mTheory;

	/**
	 * stores the information from literals of the form "variable = constant".
	 * Instantiations that contain the corresponding substitution cannot be a
	 * conflict clause. TODO: further effect: we may want to propagate the
	 * equalities...
	 */
	HashMap<TermVariable, HashSet<ApplicationTerm>> mExceptedPoints = 
			new HashMap<TermVariable, HashSet<ApplicationTerm>>();
	
	HashSet<TermTuple> exceptedEqualities = new HashSet<>();//TODO: store in a way that better represents symmetry

	/**
	 * Tracks for each literal lit in this clause if, in the current partial
	 * model (determined through setLiteral and possibly first-order
	 * propagations), lit can still be fulfilled. (Example: literal (not (P x
	 * y)) cannot be fulfilled after setting (P c d))
	 * 
	 * Special cases:
	 *  - quantified equalities are not tracked -- we just consider the eprLiterals 
	 *    modulo those exceptions. 
	 *    (? does this work? an alternative would be to unit-propagate those 
	 *      equalities, too, TODO: think about it..)
	 *  - for non EprLiterals this coincides with their state in the DPLLEngine
	 *    (so "fulfillable" means "true" here)
	 */
//	private HashMap<Literal, Boolean> mFulfillabilityStatus = new HashMap<Literal, Boolean>();
	
	EprStateManager mStateManager;
	EqualityManager mEqualityManager;
	boolean forcesFiniteModel = false;

	public EprClause(Literal[] literals, Theory theory, 
			EprStateManager stateManager, boolean freshAlphaRenamed, TTSubstitution freshAlphaRen) {
		super(literals);
		mTheory = theory;
		mStateManager = stateManager;
		mEqualityManager = stateManager.mEqualityManager;
		this.isFreshAlphaRenamed = freshAlphaRenamed;
		this.mFreshAlphaRenaming = freshAlphaRen;
		setUpClause(literals);
	}

	public EprClause(Literal[] literals, ProofNode proof, Theory theory) {
		super(literals, proof);
		throw new UnsupportedOperationException();
	}

	public EprClause(Literal[] literals, int stacklevel, Theory theory) {
		super(literals, stacklevel);
		throw new UnsupportedOperationException();
	}

	public EprClause(Literal[] literals, ResolutionNode proof, int stacklevel, Theory theory) {
		super(literals, proof, stacklevel);
		throw new UnsupportedOperationException();
	}

	private void setUpClause(Literal[] literals) {
	
		for (Literal l : literals) {
			if (mAllLiterals.contains(l.negate()))
				isTautology = true;
			if (l instanceof TrueAtom)
				isTautology = true;
			if (l instanceof CCEquality 
					&& ((CCEquality) l).getLhs().equals(((CCEquality) l).getRhs()))
				isTautology = true; // l is of the form (= c c)
			if (l instanceof EprGroundEqualityAtom
					&& ((EprGroundEqualityAtom) l).getArguments()[0].equals(((EprGroundEqualityAtom) l).getArguments()[1]));
				isTautology = true; // l is of the form (= c c)
			mAllLiterals.add(l);
		}
		//TODO:
		// as an optimization perhaps stop here if isTautology is true.

	
		// sort the literals into the different categories
		sortLiterals(literals);
		
		// do we have quantified equalities but no other quantified literals?
		if (eprQuantifiedEqualityAtoms.length > 0 
				&& eprQuantifiedPredicateLiterals.length == 0) {
			forcesFiniteModel = true;
		}
		
		// collect the free vars occuring in this clause
		for (Literal l : eprQuantifiedPredicateLiterals)
			mFreeVars.addAll(((EprQuantifiedPredicateAtom) l.getAtom())
					.getArgumentsAsTermTuple().getFreeVars());
		for (Literal l : eprQuantifiedEqualityAtoms)
			mFreeVars.addAll(((EprQuantifiedEqualityAtom) l.getAtom())
					.getArgumentsAsTermTuple().getFreeVars());
		
		//the equalities are handled separately
		mAllLiterals.removeAll(Arrays.asList(eprQuantifiedEqualityAtoms));

	}





	private static boolean doesUnifierChangeTheClause(TTSubstitution sub, EprClause eprClause) {
		if (sub.isEmpty())
			return false;
		HashSet<TermVariable>  fvIntersection = new HashSet<>(sub.tvSet());
		fvIntersection.retainAll(eprClause.getFreeVars());
		
		if (fvIntersection.isEmpty())
			return false;

		return true;
	}

	protected HashSet<TermVariable> getFreeVars() {
		return mFreeVars;
	}

	public boolean isGround() {
		return eprQuantifiedPredicateLiterals.length == 0;
	}


	private boolean subset(HashMap<TermVariable, HashSet<ApplicationTerm>> eps1,
			HashMap<TermVariable, HashSet<ApplicationTerm>> eps2) {
		for (Entry<TermVariable, HashSet<ApplicationTerm>> en1 : eps1.entrySet()) {
			if (!eps2.containsKey(en1.getKey()))
				if (!en1.getValue().isEmpty())
					return false;
				else
					continue;
			HashSet<ApplicationTerm> set1 = en1.getValue();
			HashSet<ApplicationTerm> set2 = eps2.get(en1.getKey());
			if (!set2.containsAll(set1))
				return false;
		}
		return true;
	}

	private void sortLiterals(Literal[] literals) {
		int noQuantifiedEqualities = 0;
		int noQuantifiedPredicates = 0;
		int noOthers = 0;
		// TODO: is this (counting then making arrays) more efficient than using
		// a list?
		for (Literal l : literals) {
			if (l.getAtom() instanceof EprQuantifiedEqualityAtom) {
				// TODO: this assert is probably too strict: we have to allow
				// disequalities between quantified variables, right?
				assert l.getSign() == 1 : "Destructive equality reasoning should have eliminated this literal.";
				noQuantifiedEqualities++;
			} else if (l.getAtom() instanceof EprQuantifiedPredicateAtom) {
				noQuantifiedPredicates++;
			} else {
				noOthers++;
			}
		}

		eprQuantifiedEqualityAtoms = new EprQuantifiedEqualityAtom[noQuantifiedEqualities];
		eprQuantifiedPredicateLiterals = new Literal[noQuantifiedPredicates];
		groundLiterals = new Literal[noOthers];

		// TODO: reusing the counter as array index may be unnecessarily
		// confusing..
		for (Literal l : literals) {
			if (l.getAtom() instanceof EprQuantifiedEqualityAtom) {
				assert l.getSign() == 1 : "negated quantified equality should have been removed by DER";
//				eprEqualityLiterals[--noQuantifiedEqualities] = l;
				eprQuantifiedEqualityAtoms[--noQuantifiedEqualities] = (EprQuantifiedEqualityAtom) l;
//			} else if (l.getAtom() instanceof EprPredicateAtom) {
			} else if (l.getAtom() instanceof EprQuantifiedPredicateAtom) {
				// Have the EprPredicates point to the clauses and literals
				// they occur in.
				EprPredicate pred = ((EprPredicateAtom) l.getAtom()).eprPredicate;
				pred.addQuantifiedOccurence(l, this);

				eprQuantifiedPredicateLiterals[--noQuantifiedPredicates] = l;
			} else {
				groundLiterals[--noOthers] = l;
			}
		}

		for (Literal l : eprQuantifiedEqualityAtoms) {
			Term p0 = ((ApplicationTerm) ((EprQuantifiedEqualityAtom) l.getAtom()).getTerm()).getParameters()[0];
			Term p1 = ((ApplicationTerm) ((EprQuantifiedEqualityAtom) l.getAtom()).getTerm()).getParameters()[1];
			if (p0 instanceof TermVariable && p1 instanceof TermVariable) {
				addExceptedEquality((TermVariable) p0, (TermVariable) p1);
			} else if (p0 instanceof TermVariable) {
				updateExceptedPoints((TermVariable) p0, (ApplicationTerm) p1);
			} else if (p1 instanceof TermVariable) {
				updateExceptedPoints((TermVariable) p1, (ApplicationTerm) p0);
			} else {
				assert false : "this equation should have gone to CClosure Theory: " + l.getAtom();
			}
		}
	}

	private void addExceptedEquality(TermVariable p0, TermVariable p1) {
		exceptedEqualities.add(new TermTuple(new Term[] { p0 , p1 }));
	}

	private void updateExceptedPoints(TermVariable tv, ApplicationTerm at) {
		HashSet<ApplicationTerm> exceptions = mExceptedPoints.get(tv);
		if (exceptions == null) {
			exceptions = new HashSet<>();
			mExceptedPoints.put(tv, exceptions);
		}
		exceptions.add(at);
	}


	public EprClause instantiateClause(TTSubstitution sub) {
		return instantiateClause(null, sub, null);
	}
	/**
	 * Create a new clause that is gained from applying the substitution sub to all literals in this clause.
	 * otherLit is omitted (typically because it is the pivot literal of a resolution).
	 * @param otherLit
	 * @param sub
	 * @return
	 */
	public EprClause instantiateClause(Literal otherLit, TTSubstitution sub) {
		return instantiateClause(otherLit, sub, null);
	}

	/**
	 * Create a new clause that is gained from applying the substitution sub to all literals in this clause.
	 * otherLit is omitted (typically because it is the pivot literal of a resolution).
	 * 
	 * @param otherLit
	 * @param sub
	 * @param additionalLiterals a list of literals that are added to the clause 
	 *       (we may want to express it holds under certain preconditions for instance..)
	 * @return
	 */
	public EprClause instantiateClause(Literal otherLit, TTSubstitution sub, ArrayList<Literal> additionalLiterals) {
		ArrayList<Literal> newLits = getSubstitutedLiterals(sub);
		
		if (otherLit != null)
			newLits.remove(otherLit);
		
		if (additionalLiterals != null)
			newLits.addAll(additionalLiterals);
		
		return mStateManager.getDerivedClause(new HashSet<Literal>(newLits), mTheory, this);
	}

	protected ArrayList<Literal> getSubstitutedLiterals(TTSubstitution sub) {
		ArrayList<Literal> newLits = new ArrayList<Literal>();
		newLits.addAll(Arrays.asList(groundLiterals));
		for (Literal l : eprQuantifiedEqualityAtoms) {
			newLits.add(EprHelpers.applySubstitution(sub, l, mTheory));
		}
		for (Literal l : eprQuantifiedPredicateLiterals) {
			newLits.add(EprHelpers.applySubstitution(sub, l, mTheory));
		}
		return newLits;
	}




	/**
	 * A unifier (substitution) is trivial wrt. two TermTuples
	 *   iff 
	 *  (- it only substitues variables with variables)
	 *  - each TermTuple has the same number of variables after unification as before
	 * @param sub
	 * @return
	 */
	public static boolean isUnifierJustARenaming(TTSubstitution sub, TermTuple tt1, TermTuple tt2) {
		if (sub.apply(tt1).getFreeVars().size() != tt1.getFreeVars().size())
			return false;
		if (sub.apply(tt2).getFreeVars().size() != tt2.getFreeVars().size())
			return false;
		return true;
	}

	/**
	 * Idea:
	 *  - We start with a clause where all, or all but one, literals L are labelled as "unfulfillable".
	 *  - Each unfulfillable literal has one or more reasons of unfulfillability, a reason of unfulfillability is
	 *     an EprUnitClause that is set in the current state.
	 *  - We are looking for substitutions that at the same time
	 *    -- unify all the literals L
	 *    -- unify each literal in L with one of its conflict points
	 *    -- don't introduce excepted points 
	 *        (excepted through a quantified equality literal in the base clause 
	 *         or in the EprQuantifiedUnitClause of a corresponding conflict point)
	 * 
	 * @author alex
	 *
	 */
	class ComputeClauseUnifiers {
		private HashMap<TTSubstitution, ArrayList<ArrayList<TermTuple>>> mSubstitutionToInstantiations = new HashMap<>();
		
		HashSet<EprQuantifiedEqualityAtom> mExceptionsFromClause;
		HashSet<TTSubstitution> mSubstitutions;
		
		public ComputeClauseUnifiers(
				ArrayDeque<Pair<TermTuple, HashSet<EprUnitClause>>> clauseLitPointToUnfulReasons, 
				EprQuantifiedEqualityAtom[] exceptedEqualities) { 
			mExceptionsFromClause = new HashSet<>(Arrays.asList(exceptedEqualities));
			mSubstitutions = new HashSet<>();
			computeInstantiations(clauseLitPointToUnfulReasons, new TTSubstitution(), true);
		}
	
		/**
		 * 
		 * @param partialInstantiations the instantiations collected so far (an instantiation is a sequence of points that fit the literals 
		 *           of this clause that have been processed so far)
		 * @param clauseLitTTToUnfulReasons A list of pairs wher
		 *    the first entry is a termtuple that comes from a literal in the clause where this is called from
		 *    the second entry is a list of conflicting EprUnitClauses 
		 *      --> note that we have to check upfront that these are really conflicting wrt polarity and predicateSymbol
		 * @param exceptedEqualities Equalities that mark exceptions mad in the clause where the clauseLitTermTuples come from
		 * @param substitution the unifier of the current instantiation -- further unification may only be a specialization
		 *                  (new for the unit clause case: this should not necessarily be a substitution that grounds everything.. 
		 *                      -- computeConflictClause may always ground by adding lambdas, for example..)

		 * @param isFirstCall the first call is special, because there are no instantiations to build upon
		 */
		private void computeInstantiations(
//				ArrayList<ArrayList<TermTuple>> partialInstantiations,
				ArrayDeque<Pair<TermTuple, HashSet<EprUnitClause>>> clauseLitTTToUnfulReasons,
				TTSubstitution substitution, boolean isFirstCall) {
			// TODO: might be better to rework this as NonRecursive

			if (clauseLitTTToUnfulReasons.isEmpty()) {
//				mSubstitutionToInstantiations.put(substitution, partialInstantiations);
				return;
			}
			
			Pair<TermTuple, HashSet<EprUnitClause>> currentPair = clauseLitTTToUnfulReasons.pollFirst();

			TermTuple currentClauseLitTT = currentPair.first;
			HashSet<EprUnitClause> currentUnfulReasons = currentPair.second;

			for (EprUnitClause conflict : currentUnfulReasons) {
				TTSubstitution newSubs = currentClauseLitTT.match(
						conflict.getPredicateAtom().getArgumentsAsTermTuple(), 
						new TTSubstitution(substitution), 
						mEqualityManager);
				
				HashSet<EprQuantifiedEqualityAtom> currentExceptions = 
						new HashSet<>();
				currentExceptions.addAll(mExceptionsFromClause);
				currentExceptions.addAll(Arrays.asList(conflict.eprQuantifiedEqualityAtoms));

				if (newSubs == null) 
					continue;
				if (isSubstitutionExcepted(newSubs, currentExceptions)) 
					continue;

				computeInstantiations(
						new ArrayDeque<Pair<TermTuple, HashSet<EprUnitClause>>>(clauseLitTTToUnfulReasons),
						newSubs, 
						false);
			}
		}

		/**
		 * checks is the given substitution refers to an instantiation of the
		 * quantified variables that is excepted through an equality literal in the
		 * clause (e.g. the clause says {... v x = c}, then an instantiation that
		 * maps x to c cannot violate the clause)
		 * 
		 * returns true iff newSubs corresponds to at least one excepted point
		 */
		private boolean isSubstitutionExcepted(TTSubstitution newSubs, Collection<EprQuantifiedEqualityAtom> exceptedEqualities) {
			// check exceptions of the form (= x c), i.e., with exactly one quantified variable
			for (SubsPair en : newSubs.getSubsPairs()) {
				for (EprQuantifiedEqualityAtom eqea : exceptedEqualities) { //TODO: a faster variant
					if ((en.top == eqea.getLhs() && en.bot == eqea.getRhs())
							&& (en.bot == eqea.getLhs() && en.top == eqea.getRhs())) {
						return true;
					}
				}
			}
			return false;
		}
		
		public HashSet<TTSubstitution> getSubstitutions() {
			return mSubstitutions;
		}
	}

	public HashSet<Literal> getLiteralSet() {
		return mAllLiterals;
	}
	
	public boolean forcesFiniteModel() {
		assert !isFreshAlphaRenamed;
		return forcesFiniteModel;
	}
	
	public abstract boolean isConflictClause();
	
	public abstract EprUnitClause getUnitClauseLiteral();
	
	public boolean isTautology() {
		return isTautology;
	}
	
	public Literal[] getQuantifiedPredicateLiterals() {
		return eprQuantifiedPredicateLiterals;
	}
	
	public Literal[] getGroundLiterals() {
		return groundLiterals;
	}
	
	public EprQuantifiedEqualityAtom[] getEqualityAtoms() {
		return eprQuantifiedEqualityAtoms;
	}
	
	public abstract EprClause getFreshAlphaRenamedVersion();

	protected ArrayList<Literal> getFreshAlphaRenamedLiterals(TTSubstitution sub) {
//		TTSubstitution sub = new TTSubstitution();
		for (TermVariable fv : this.getFreeVars()) {
			sub.addSubs(mTheory.createFreshTermVariable(fv.getName(), fv.getSort()), fv);
		}
		
		ArrayList<Literal> newLits = getSubstitutedLiterals(sub);
		return newLits;
	}
	
	public TTSubstitution getFreshAlphaRenaming() {
		assert isFreshAlphaRenamed;
		return mFreshAlphaRenaming;
	}

//	public EprClause getFreshAlphaRenamedVersion(TTSubstitution freshAlphaRen) {
//		// TODO Auto-generated method stub
//		return null;
//	}
}
