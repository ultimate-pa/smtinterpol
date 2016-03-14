package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode;

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
public class EprClause extends Clause {

	Literal[] eprEqualityLiterals;
	Literal[] eprQuantifiedPredicateLiterals;
	Literal[] groundLiterals;

	Theory mTheory;

	/**
	 * stores the information from literals of the form "variable = constant".
	 * Instantiations that contain the corresponding substitution cannot be a
	 * conflict clause. TODO: further effect: we may want to propagate the
	 * equalities...
	 */
	HashMap<TermVariable, ArrayList<ApplicationTerm>> mExceptedPoints = new HashMap<TermVariable, ArrayList<ApplicationTerm>>();
	
//	int mClauseIndex = 0;

	private Literal mUnitLiteral;

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
	private HashMap<Literal, Boolean> mFulfillabilityStatus = new HashMap<Literal, Boolean>();
	private int mNoFulfillableLiterals;
	
	HashSet<Literal> mFulfilledLiterals = new HashSet<Literal>();

	// HashMap<Literal, HashMap<Integer, ArrayList<ApplicationTerm>>>
	// mExceptedPointsPerLiteral =
	// new HashMap<Literal, HashMap<Integer, ArrayList<ApplicationTerm>>>();

	public EprClause(Literal[] literals, Theory theory, int clauseIndex) {
		super(literals);
		mTheory = theory;
		setUpClause(literals, clauseIndex);
	}

	public EprClause(Literal[] literals, ProofNode proof, Theory theory) {
		super(literals, proof);
		throw new UnsupportedOperationException();
//		mTheory = theory;
//		setUpClause(literals);
	}

	public EprClause(Literal[] literals, int stacklevel, Theory theory) {
		super(literals, stacklevel);
		throw new UnsupportedOperationException();
//		mTheory = theory;
//		setUpClause(literals);
	}

	public EprClause(Literal[] literals, ResolutionNode proof, int stacklevel, Theory theory) {
		super(literals, proof, stacklevel);
		throw new UnsupportedOperationException();
//		mTheory = theory;
//		setUpClause(literals);
	}

	private void setUpClause(Literal[] literals, int clauseIndex) {
		
		// for propagation later, we want the variables in each clause (i.e., quantifier scope) to be unique
		literals = doAlphaRenaming(literals, clauseIndex);

		// is this a unit clause upon creation?
		if (literals.length == 1) {
			mUnitLiteral = literals[0];
		}

		// sort the literals into the different categories
		sortLiterals(literals);

		// set fulfillability status
		mNoFulfillableLiterals = 0;
		for (Literal li : eprQuantifiedPredicateLiterals) {
			setLiteralFulfillable(li);
		}
	}

	private Literal[] doAlphaRenaming(Literal[] literals, int clauseIndex) {
		Literal[] result = new Literal[literals.length];
		
		//TODO --> best do this in clausifier, right?
		
		return result;
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

		eprEqualityLiterals = new Literal[noQuantifiedEqualities];
		eprQuantifiedPredicateLiterals = new Literal[noQuantifiedPredicates];
		groundLiterals = new Literal[noOthers];

		// TODO: reusing the counter as array index may be unnecessarily
		// confusing..
		for (Literal l : literals) {
			if (l.getAtom() instanceof EprEqualityAtom) {
				eprEqualityLiterals[--noQuantifiedEqualities] = l;
//			} else if (l.getAtom() instanceof EprPredicateAtom) {
			} else if (l.getAtom() instanceof EprQuantifiedPredicateAtom) {
//				if (((EprPredicateAtom) l.getAtom()).isQuantified) {
					// Have the EprPredicates point to the clauses and literals
					// they occur in.
					EprPredicate pred = ((EprPredicateAtom) l.getAtom()).eprPredicate;
					pred.addQuantifiedOccurence(l, this);
//				}
				eprQuantifiedPredicateLiterals[--noQuantifiedPredicates] = l;
			} else {
				groundLiterals[--noOthers] = l;
			}
		}

		for (Literal l : eprEqualityLiterals) {
			Term p0 = ((ApplicationTerm) ((EprEqualityAtom) l.getAtom()).mTerm).getParameters()[0];
			Term p1 = ((ApplicationTerm) ((EprEqualityAtom) l.getAtom()).mTerm).getParameters()[1];
			if (p0 instanceof TermVariable && p1 instanceof TermVariable) {
				throw new UnsupportedOperationException("todo: implement");
			} else if (p0 instanceof TermVariable) {
				updateExceptedPoints((TermVariable) p0, (ApplicationTerm) p1);
			} else if (p1 instanceof TermVariable) {
				updateExceptedPoints((TermVariable) p1, (ApplicationTerm) p0);
			} else {
				assert false : "this equation should have gone to CClosure Theory: " + l.getAtom();
			}
		}
	}

	private void updateExceptedPoints(TermVariable tv, ApplicationTerm at) {
		ArrayList<ApplicationTerm> exceptions = mExceptedPoints.get(tv);
		if (exceptions == null) {
			exceptions = new ArrayList<>();
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
	public Clause check() {

		ArrayDeque<HashSet<TermTuple>> conflictPointSets = new ArrayDeque<>();

		for (Literal l : eprQuantifiedPredicateLiterals) {
			EprPredicateAtom epa = (EprPredicateAtom) l.getAtom();
			EprPredicate ep = epa.eprPredicate;

			HashSet<TermTuple> potentialConflictPoints = l.getSign() == 1 ? ep.mNegativelySetPoints
					: ep.mPositivelySetPoints;

			conflictPointSets.add(potentialConflictPoints);
		}

		// TODO: take excepted points into account

		ArrayDeque<TermTuple> pointsFromLiterals = computePointsFromLiterals(eprQuantifiedPredicateLiterals);

		ArrayList<ArrayList<TermTuple>> instantiations = computeInstantiations(new ArrayList<ArrayList<TermTuple>>(),
				conflictPointSets, pointsFromLiterals, new HashMap<TermVariable, Term>(), true);

		// if there is a fitting instantiation, it directly induces a conflict
		// clause
		if (instantiations.isEmpty()) {
			return null;
		} else {
			ArrayList<EprPredicate> predicates = computePredicatesFromLiterals(eprQuantifiedPredicateLiterals);
			ArrayList<Boolean> polaritites = computePolaritiesFromLiterals(eprQuantifiedPredicateLiterals);
			return clauseFromInstantiation(predicates, instantiations.get(0), polaritites);
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
	 * compute a filtered cross product
	 * 
	 * @param pointsFromLiterals
	 */
	private ArrayList<ArrayList<TermTuple>> computeInstantiations(ArrayList<ArrayList<TermTuple>> instantiations,
			ArrayDeque<HashSet<TermTuple>> conflictPointSets, ArrayDeque<TermTuple> pointsFromLiterals,
			HashMap<TermVariable, Term> substitution, boolean isFirstCall) {
		// TODO: might be better to rework this as NonRecursive

		if (conflictPointSets.isEmpty())
			return instantiations;

		HashSet<TermTuple> currentPoints = conflictPointSets.pollFirst();
		TermTuple currentPfl = pointsFromLiterals.pollFirst();

		for (TermTuple tt : currentPoints) {
			HashMap<TermVariable, Term> newSubs = new HashMap<TermVariable, Term>(substitution);
			newSubs = tt.match(currentPfl, newSubs);

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
					for (ArrayList<TermTuple> in : instantiations) {
						ArrayList<TermTuple> inNew = new ArrayList<>(in);
						inNew.add(tt);
						instantiationsNew.add(inNew);
					}
				}
				return computeInstantiations(instantiationsNew, new ArrayDeque<HashSet<TermTuple>>(conflictPointSets),
						new ArrayDeque<TermTuple>(pointsFromLiterals), newSubs, false);
			}
		}
		return new ArrayList<ArrayList<TermTuple>>();
	}

	/**
	 * checks is the given substitution refers to an instantiation of the
	 * quantified variables that is excepted through an equality literal in the
	 * clause (e.g. the clause says {... v x = c}, then an instantiation that
	 * maps x to c cannot violate the clause)
	 * 
	 * returns true iff newSubs corresponds to at least one excepted point
	 */
	private boolean isSubstitutionExcepted(HashMap<TermVariable, Term> newSubs) {
		for (Entry<TermVariable, Term> en : newSubs.entrySet()) {
			ArrayList<ApplicationTerm> epCon = mExceptedPoints.get(en.getKey());
			if (epCon != null && epCon.contains(en.getValue()))
				return true;
		}
		return false;
	}

	public Literal getUnitClauseLiteral() {
		assert mUnitLiteral != null;

		return this.mUnitLiteral;
	}

	public void setLiteralUnfulfillable(Literal lit) {
		mFulfillabilityStatus.put(lit, false);
		mNoFulfillableLiterals--;
		if (mNoFulfillableLiterals == 1) {
			//TODO: this could be done more efficiently i guess..
			for (Literal li : eprQuantifiedPredicateLiterals) {
				if (mFulfillabilityStatus.get(li)) {
					mUnitLiteral = li;
					break;
				}
			}
		}

	}

	public void setLiteralFulfillable(Literal li) {
		mFulfillabilityStatus.put(li, true);
		mNoFulfillableLiterals++;
		if (mNoFulfillableLiterals == 2) {
			mUnitLiteral = null;
		}
	}
	
	
//	public void setLiteralFulfilled(Literal li) {
//		
//	}
	
	public boolean isUnitClause() {
		return mUnitLiteral != null;
	}

	public void setGroundLiteral(Literal literal) {
		for (Literal li : groundLiterals) {
			if (literal.getAtom().equals(li.getAtom())) {
				if (literal.getSign() == li.getSign()) {
					setLiteralFulfillable(li);
					mFulfilledLiterals.add(li);
				} else {
					setLiteralUnfulfillable(li);
					mFulfilledLiterals.remove(li);
				}
			}
		}
	
	}

	public void unsetGroundLiteral(Literal literal) {
		for (Literal li : groundLiterals) {
			if (literal.getAtom().equals(li.getAtom())) {
				if (literal.getSign() == li.getSign()) {
					// was fulfillable after set (bc true), is still fulfillable after unset (bc unconstrained)
					mFulfilledLiterals.remove(li);
				} else {
//					setLiteralUnfulfillable(li);
					// was unfulfillable after set (bc false), is fulfillable now (bc unconstrained)
					setLiteralFulfillable(li);
					//was not fulfilled after set, is still not fulfilled now.
//					mFulfilledLiterals.remove(li);
				}
			}
		}
	}

	/**
	 * @return true if at least one of the literals of this clause is definitely true.
	 */
	public boolean isFulfilled() {
		return mFulfilledLiterals.size() > 0;
	}

	public void setQuantifiedLiteral(Literal unitLiteral) {
		boolean positive = unitLiteral.getSign() == 1;
		EprPredicateAtom atom = (EprPredicateAtom) unitLiteral.getAtom();
		
		ArrayList<Literal> predicateLiterals = new ArrayList<>();
		predicateLiterals.addAll(Arrays.asList(eprQuantifiedPredicateLiterals));
		for (Literal l : groundLiterals) 
			if (l instanceof EprGroundPredicateAtom)
				predicateLiterals.add(l);
		
		for (Literal otherLit : predicateLiterals) {
			boolean otherPositive = otherLit.getSign() == 1;
			EprPredicateAtom otherAtom = (EprPredicateAtom) otherLit.getAtom();
			boolean otherIsQuantified = otherAtom instanceof EprQuantifiedPredicateAtom;

			// do the eprPredicates match? do nothing if they don't
			if (!otherAtom.eprPredicate.equals(atom.eprPredicate)) 
				continue;

			// is there a unifier?
			TermTuple atomArgs = atom.getArgumentsAsTermTuple();
			TermTuple otherArgs = otherAtom.getArgumentsAsTermTuple();
			HashMap<TermVariable, Term> sub = otherArgs.match(atomArgs);

			// if there is no unifier, do nothing
			if (sub == null)
				continue;
			
			// if the unifier is trivial, update this clauses satisfiability status accordingly
			if (isUnifierTrivial(sub, atomArgs, otherArgs)) {
				
				// if the signs match, the clause is fulfilled
				if (positive == otherPositive
						&& otherIsQuantified) {
					//setLiteralFulfilled
				} else if (positive != otherPositive
						&& otherIsQuantified) {
					setLiteralUnfulfillable(otherLit);
				} else if (positive == otherPositive
						&& !otherIsQuantified) {

				} else {
					// 

				}
			
				continue;
			} else {
				// if the unifier is non-trivial, create a new clause
				
			}
			
		}
	}

	/**
	 * A unifier (substitution) is trivial wrt. two TermTuples
	 *   iff 
	 *  (- it only substitues variables with variables)
	 *  - each TermTuple has the same number of variables after unification as before
	 * @param sub
	 * @return
	 */
	private boolean isUnifierTrivial(HashMap<TermVariable, Term> sub, TermTuple tt1, TermTuple tt2) {
		if (tt1.applySubstitution(sub).getFreeVars().size() != tt1.getFreeVars().size())
			return false;
		if (tt2.applySubstitution(sub).getFreeVars().size() != tt2.getFreeVars().size())
			return false;
		return true;
	}

}
