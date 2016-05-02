package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution.SubsPair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution.TPair;

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
	
	enum FulfillabilityStatus { Fulfilled, Fulfillable, Unfulfillable };

	EprEqualityAtom[] eprEqualityAtoms;
	Literal[] eprQuantifiedPredicateLiterals;
	Literal[] groundLiterals;
	
	/**
	 * used for
	 *  - debugging
	 *  - finding tautologies
	 */
	HashSet<Literal> mAllLiterals = new HashSet<>();
	
	boolean isTautology = false;

	Theory mTheory;

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

	public EprClause(Literal[] literals, Theory theory, EprStateManager stateManager) {
		super(literals);
		mTheory = theory;
		mStateManager = stateManager;
		mEqualityManager = stateManager.mEqualityManager;
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
			if (l.equals(new TrueAtom()))
				isTautology = true;
			if (l instanceof CCEquality 
					&& ((CCEquality) l).getLhs().equals(((CCEquality) l).getRhs()))
				isTautology = true; // l is of the form (= c c)
			mAllLiterals.add(l);
		}
		//TODO:
		// as an optimization perhaps stop here if isTautology is true.

	
		// sort the literals into the different categories
		sortLiterals(literals);
		
		// do we have quantified equalities but no other quantified literals?
		if (eprEqualityAtoms.length > 0 
				&& eprQuantifiedPredicateLiterals.length == 0) {
			assert false : "TODO: probably do something -- sth with finite models..";
		}
		

		
		//the equalities are handled separately
		mAllLiterals.removeAll(Arrays.asList(eprEqualityAtoms));

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

	private HashSet<TermVariable> getFreeVars() {
		HashSet<TermVariable> result = new HashSet<>();
		for (Literal l : eprQuantifiedPredicateLiterals) {
			result.addAll(((EprQuantifiedPredicateAtom) l.getAtom()).getArgumentsAsTermTuple().getFreeVars());
		}
		return result;
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
			if (l.getAtom() instanceof EprEqualityAtom) {
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

		eprEqualityAtoms = new EprEqualityAtom[noQuantifiedEqualities];
		eprQuantifiedPredicateLiterals = new Literal[noQuantifiedPredicates];
		groundLiterals = new Literal[noOthers];

		// TODO: reusing the counter as array index may be unnecessarily
		// confusing..
		for (Literal l : literals) {
			if (l.getAtom() instanceof EprEqualityAtom) {
				assert l.getSign() == 1 : "negated quantified equality should have been removed by DER";
//				eprEqualityLiterals[--noQuantifiedEqualities] = l;
				eprEqualityAtoms[--noQuantifiedEqualities] = (EprEqualityAtom) l;
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

		for (Literal l : eprEqualityAtoms) {
			Term p0 = ((ApplicationTerm) ((EprEqualityAtom) l.getAtom()).mTerm).getParameters()[0];
			Term p1 = ((ApplicationTerm) ((EprEqualityAtom) l.getAtom()).mTerm).getParameters()[1];
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

	/**
	 * Checks if this clause is fulfilled in the current decide state wrt. the
	 * EPR theory.
	 * 
	 * @return null if this clause is fulfilled, a conflict clause otherwise
	 */
	public Clause check(EprStateManager esm) {

		ArrayDeque<HashSet<TermTuple>> conflictPointSets = new ArrayDeque<>();

		for (Literal l : eprQuantifiedPredicateLiterals) {
			EprPredicateAtom epa = (EprPredicateAtom) l.getAtom();
			EprPredicate ep = epa.eprPredicate;

			HashSet<TermTuple> potentialConflictPoints = esm.getPoints(l.getSign() == 1, ep);

			conflictPointSets.add(potentialConflictPoints);
		}

		// TODO: take excepted points into account

		ArrayDeque<TermTuple> pointsFromLiterals = computePointsFromLiterals(eprQuantifiedPredicateLiterals);

//		ArrayList<ArrayList<TermTuple>> instantiations = computeInstantiations(new ArrayList<ArrayList<TermTuple>>(),
//				conflictPointSets, pointsFromLiterals, new HashMap<TermVariable, Term>(), true);
		ArrayList<TermTuple> instantiation = new ComputeInstantiations(conflictPointSets, pointsFromLiterals).getInstantiation();
		// if there is a fitting instantiation, it directly induces a conflict
		// clause
//		if (instantiations.isEmpty()) {
		if (instantiation == null) {
			return null;
		} else {
			ArrayList<EprPredicate> predicates = computePredicatesFromLiterals(eprQuantifiedPredicateLiterals);
			ArrayList<Boolean> polaritites = computePolaritiesFromLiterals(eprQuantifiedPredicateLiterals);
//			return clauseFromInstantiation(predicates, instantiations.get(0), polaritites);
			return clauseFromInstantiation(predicates, instantiation, polaritites);
		}
	}

	private Clause clauseFromInstantiation(ArrayList<EprPredicate> predicates, ArrayList<TermTuple> points,
			ArrayList<Boolean> polarities) {
		ArrayList<Literal> result = new ArrayList<Literal>();
		for (int i = 0; i < predicates.size(); i++) {
			// EprPredicateAtom epa = new EprPredicateAtom(
			// mTheory.term(predicates.get(i).functionSymbol,
			// points.get(i).terms),
			// 0, 0, predicates.get(i));//TODO replace 0, 0
			EprPredicateAtom epa = predicates.get(i).getAtomForPoint(points.get(i));

			result.add(polarities.get(i) ? epa : epa.negate());
		}

		return new Clause(result.toArray(new Literal[result.size()]));
	}

	private ArrayList<EprPredicate> computePredicatesFromLiterals(Literal[] eprPredicateLiterals2) {
		// TODO cache/precompute this
		ArrayList<EprPredicate> result = new ArrayList<EprPredicate>();
		for (Literal l : eprPredicateLiterals2) {
			result.add(((EprPredicateAtom) l.getAtom()).eprPredicate);
		}
		return result;
	}

	private ArrayList<Boolean> computePolaritiesFromLiterals(Literal[] eprPredicateLiterals2) {
		// TODO cache/precompute this
		ArrayList<Boolean> result = new ArrayList<Boolean>();
		for (Literal l : eprPredicateLiterals2) {
			result.add(l.getSign() == 1);
		}
		return result;
	}

	private ArrayDeque<TermTuple> computePointsFromLiterals(Literal[] predicateLiterals) {
		// TODO cache/precompute this
		ArrayDeque<TermTuple> result = new ArrayDeque<>();
		for (Literal l : predicateLiterals) {
			result.add(new TermTuple(((ApplicationTerm) ((EprPredicateAtom) l.getAtom()).mTerm).getParameters()));

		}
		return result;
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
		ArrayList<Literal> newLits = new ArrayList<Literal>();
		newLits.addAll(Arrays.asList(groundLiterals));
		for (Literal l : eprEqualityAtoms) {
			newLits.add(EprHelpers.applySubstitution(sub, l, mTheory));
		}
		for (Literal l : eprQuantifiedPredicateLiterals) {
			if (l.equals(otherLit))
				continue;
			newLits.add(EprHelpers.applySubstitution(sub, l, mTheory));
		}
		
		if (additionalLiterals != null)
			newLits.addAll(additionalLiterals);
		
		return mStateManager.getDerivedClause(new HashSet<Literal>(newLits), mTheory, this);
	}




	/**
	 * A unifier (substitution) is trivial wrt. two TermTuples
	 *   iff 
	 *  (- it only substitues variables with variables)
	 *  - each TermTuple has the same number of variables after unification as before
	 * @param sub
	 * @return
	 */
//	private boolean isUnifierTrivial(HashMap<TermVariable, Term> sub, TermTuple tt1, TermTuple tt2) {
	public static boolean isUnifierJustARenaming(TTSubstitution sub, TermTuple tt1, TermTuple tt2) {

		
//		if (tt1.applySubstitution(sub).getFreeVars().size() != tt1.getFreeVars().size())
		if (sub.apply(tt1).getFreeVars().size() != tt1.getFreeVars().size())
			return false;
//		if (tt2.applySubstitution(sub).getFreeVars().size() != tt2.getFreeVars().size())
		if (sub.apply(tt2).getFreeVars().size() != tt2.getFreeVars().size())
			return false;
		return true;
	}

//	/**
//	 * 
//	 */
//	public void updateClauseState(EprStateManager eprStateManager) {
//		for (EprQuantifiedLitWExcptns eqlwe : eprStateManager.getSetLiterals()) {
//			setQuantifiedLiteral(eqlwe);
//		}
//	}
	
//	class UnFulReason {
//
//		public UnFulReason(Literal li) {
//			assert !(li.getAtom() instanceof EprQuantifiedPredicateAtom) : 
//				"probably better to use an eqlwe in this case";
//			mLiteral = li;
//			mqlwe = null;
//		}
//
//		public UnFulReason(EprQuantifiedLitWExcptns qlwe) {
//			mLiteral = null;
//			mqlwe = qlwe;
//		}
//		
//		final Literal mLiteral;
//		final EprQuantifiedLitWExcptns mqlwe;
//		
//		/**
//		 * returns just the literal form this UnFulReason.
//		 */
//		public Literal getLiteral() {
//			if (mLiteral != null)
//				return mLiteral;
//			else
//				return mqlwe.getPredicateLiteral();
//		}
//		
//		@Override
//		public String toString() {
//			return mLiteral == null ? mqlwe.toString() : mLiteral.toString();
//		}
//	}

	class ComputeInstantiations {
		private ArrayList<ArrayList<TermTuple>> mAllInstantiations = new ArrayList<>();
//		private HashMap<HashMap<TermVariable, Term>, ArrayList<ArrayList<TermTuple>>> mSubstitutionToInstantiations = new HashMap<>();
		private HashMap<TTSubstitution, ArrayList<ArrayList<TermTuple>>> mSubstitutionToInstantiations = new HashMap<>();

		public ComputeInstantiations(ArrayDeque<HashSet<TermTuple>> conflictPointSets, 
				ArrayDeque<TermTuple> pointsFromLiterals) { 

			computeInstantiations(new ArrayList<ArrayList<TermTuple>>(), 
					conflictPointSets, 
					pointsFromLiterals, 
//					new HashMap<TermVariable, Term>(), 
					new TTSubstitution(),
					true);
		}

		/**
		 * compute a filtered cross product
		 * 
		 * @param partialInstantiations the instantiations collected so far (an instantiation is a sequence of points that fit the literals 
		 *           of this clause that have been processed so far)
		 * @param conflictPointSets the points we are essentially building a cross product over
		 *                   (in the computeConflictClause case those are always ground, not so in the unitClause case)
		 * @param pointsFromLiterals the literal points (possibly containing variables, coming from the clause) that we match the conflictPoints with
		 * @param substitution the unifier of the current instantiation -- further unification may only be a specialization
		 *                  (new for the unit clause case: this should not necessarily be a substitution that grounds everything.. 
		 *                      -- computeConflictClause may always ground by adding lambdas, for example..)
		 * @param isFirstCall the first call is special, because there are no instantiations to build upon
		 * @return
		 */
		private void computeInstantiations(ArrayList<ArrayList<TermTuple>> partialInstantiations,
				ArrayDeque<HashSet<TermTuple>> conflictPointSets, ArrayDeque<TermTuple> pointsFromLiterals,
//				HashMap<TermVariable, Term> substitution, boolean isFirstCall) {
				TTSubstitution substitution, boolean isFirstCall) {
			// TODO: might be better to rework this as NonRecursive

			if (conflictPointSets.isEmpty()) {
				mAllInstantiations.addAll(partialInstantiations);
				mSubstitutionToInstantiations.put(substitution, partialInstantiations);
				return;
			}

			HashSet<TermTuple> currentPoints = conflictPointSets.pollFirst();
			TermTuple currentPfl = pointsFromLiterals.pollFirst();

			for (TermTuple tt : currentPoints) {
//				HashMap<TermVariable, Term> newSubs = new HashMap<TermVariable, Term>(substitution);
				TTSubstitution newSubs = new TTSubstitution(substitution);
				newSubs = tt.match(currentPfl, newSubs, mEqualityManager);

				if (isSubstitutionExcepted(newSubs)) {
					continue;
				}

				if (newSubs != null) {
					ArrayList<ArrayList<TermTuple>> instantiationsNew = new ArrayList<ArrayList<TermTuple>>();
					if (isFirstCall) {
						ArrayList<TermTuple> l = new ArrayList<TermTuple>();
						l.add(tt);
						instantiationsNew.add(l);
					} else {
						for (ArrayList<TermTuple> in : partialInstantiations) {
							ArrayList<TermTuple> inNew = new ArrayList<>(in);
							inNew.add(tt);
							instantiationsNew.add(inNew);
						}
					}
//					return computeInstantiations(instantiationsNew, new ArrayDeque<HashSet<TermTuple>>(conflictPointSets),
					computeInstantiations(instantiationsNew, new ArrayDeque<HashSet<TermTuple>>(conflictPointSets),
							new ArrayDeque<TermTuple>(pointsFromLiterals), newSubs, false);
				}
			}
//			return new ArrayList<ArrayList<TermTuple>>();
		}

		/**
		 * checks is the given substitution refers to an instantiation of the
		 * quantified variables that is excepted through an equality literal in the
		 * clause (e.g. the clause says {... v x = c}, then an instantiation that
		 * maps x to c cannot violate the clause)
		 * 
		 * returns true iff newSubs corresponds to at least one excepted point
		 */
//		private boolean isSubstitutionExcepted(HashMap<TermVariable, Term> newSubs) {
		private boolean isSubstitutionExcepted(TTSubstitution newSubs) {
//			for (Entry<TermVariable, Term> en : newSubs.entrySet()) {
			for (SubsPair en : newSubs.subs) {
//				HashSet<ApplicationTerm> epCon = mExceptedPoints.get(en.getKey());
				if (en instanceof TPair) {
					TPair tp = (TPair) en;
					HashSet<ApplicationTerm> epCon = mExceptedPoints.get(tp.tv);
					//				if (epCon != null && epCon.contains(en.getValue()))
					if (epCon != null && epCon.contains(tp.t))
						return true;
				}
			}
			return false;
		}
		
		/**
		 * Returns some (the first found) instantiation, null if there is none.
		 * @return
		 */
		public ArrayList<TermTuple> getInstantiation() {
			if (mAllInstantiations.isEmpty())
				return null;
			return mAllInstantiations.get(0);
		}
		/**
		 * Returns some (the first found) substitution, null if there is none.
		 * @return 
		 * @return
		 */
//		public HashMap<TermVariable, Term> getSubstitution() {
		public TTSubstitution getSubstitution() {
			if (mSubstitutionToInstantiations.isEmpty())
				return null;
			return mSubstitutionToInstantiations.keySet().iterator().next();
		}
	}

	public HashSet<Literal> getLiteralSet() {
		return mAllLiterals;
	}
	
	public abstract boolean isConflictClause();
	
	public abstract EprUnitClause getUnitClauseLiteral();
}
