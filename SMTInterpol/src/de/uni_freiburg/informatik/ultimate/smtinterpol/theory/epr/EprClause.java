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
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
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
	
	enum FulfillabilityStatus { Fulfilled, Fulfillable, Unfulfillable };

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
//	private HashMap<Literal, Boolean> mFulfillabilityStatus = new HashMap<Literal, Boolean>();

	private int mNoFulfillableLiterals;
//	
	HashSet<Literal> mFulfilledLiterals = new HashSet<Literal>();
	
	private HashMap<Literal, FulfillabilityStatus> mFulfillabilityStatus = new HashMap<Literal, FulfillabilityStatus>();

	/**
	 * The eprClause this clause has been instantiated from.
	 */
	EprClause mExplanation = null;

	private HashMap<Literal, HashSet<Literal>> mLiteralToUnfulfillabilityReasons = new HashMap<>();

	public EprClause(Literal[] literals, Theory theory) {
		super(literals);
		mTheory = theory;
		setUpClause(literals);
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

//	private void setUpClause(Literal[] literals, int clauseIndex) {
	private void setUpClause(Literal[] literals) {
		
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

	/**
	 * @return the only literal in the clause that is still fulfillable, null, if there is no such literal
	 */
	public Literal getUnitClauseLiteral() {
		if (!mFulfilledLiterals.isEmpty())
			return null;
		if (this.mUnitLiteral == null)
			return null;
		if (!(this.mUnitLiteral instanceof EprQuantifiedPredicateAtom))
			return this.mUnitLiteral;
		
	}

	private void searchUnitLiteral() {
		// that there is exactly one fulfillable literal is a necessary condition for this
		// clause being a unit clause ..
		assert mNoFulfillableLiterals == 1;
		// .. however, it is not a sufficient condition
		//   -- it might be that the reasons for unsatisfiability of the unfulfilled literals,
		//      together with the unfulfilled literals themselves, don't have a unifier
		//      (i.e. in the big conjunction that the quantifier is, there is no single clause
		//       that is unit)
		
		//TODO: this could be done more efficiently i guess..
		for (Literal li : eprQuantifiedPredicateLiterals) {
			if (mFulfillabilityStatus.get(li) == FulfillabilityStatus.Fulfillable) {
				mUnitLiteral = li;
				break;
			}
		}
	}

	private void setLiteralFulfillable(Literal li) {
		FulfillabilityStatus oldStatus = mFulfillabilityStatus.get(li);
		if (oldStatus == FulfillabilityStatus.Fulfilled)
			mFulfilledLiterals.remove(li);
		mFulfillabilityStatus.put(li, FulfillabilityStatus.Fulfillable);
		mNoFulfillableLiterals++;
		if (mNoFulfillableLiterals == 2) {
			mUnitLiteral = null;
		}
	}

	private void setLiteralFulfilled(Literal li) {
		FulfillabilityStatus oldStatus = mFulfillabilityStatus.get(li);
		mFulfillabilityStatus.put(li, FulfillabilityStatus.Fulfilled);
		mFulfilledLiterals.add(li);
		if (oldStatus == FulfillabilityStatus.Fulfillable) {
			mNoFulfillableLiterals--;
			if (mNoFulfillableLiterals == 1) {
				searchUnitLiteral();
			}
		}
	}
	
	private void setLiteralUnfulfillable(Literal li) {
		FulfillabilityStatus oldStatus = mFulfillabilityStatus.get(li);
		if (oldStatus == FulfillabilityStatus.Fulfilled)
			mFulfilledLiterals.remove(li);
		mFulfillabilityStatus.put(li, FulfillabilityStatus.Unfulfillable);
		if (oldStatus == FulfillabilityStatus.Fulfillable) {
			mNoFulfillableLiterals--;
			if (mNoFulfillableLiterals == 1) {
				searchUnitLiteral();
			}
		}
	}
	
	public void setQuantifiedLiteralUnfulfillable(Literal quantifiedLit, Literal reason) {
		assert quantifiedLit.getAtom() instanceof EprQuantifiedPredicateAtom;
		setLiteralUnfulfillable(quantifiedLit);
		updateLiteralToUnfulfillabilityReasons(quantifiedLit, reason);
	}

	private void updateLiteralToUnfulfillabilityReasons(Literal quantifiedLit, Literal reason) {
		HashSet<Literal> ufr = mLiteralToUnfulfillabilityReasons.get(quantifiedLit);
		if (ufr == null) {
			ufr = new HashSet<>();
			mLiteralToUnfulfillabilityReasons.put(quantifiedLit, ufr);
		}
		ufr.add(reason);
	}

	/**
	 * Upgrade the clause state to account for the fact that literal has been set.
	 * @param literal
	 */
	public void setGroundLiteral(Literal literal) {
		for (Literal li : groundLiterals) {
			if (literal.getAtom().equals(li.getAtom())) {
				if (literal.getSign() == li.getSign()) {
					setLiteralFulfilled(li);
				} else {
					setLiteralUnfulfillable(li);
				}
			}
		}
		
		if (literal.getAtom() instanceof EprGroundPredicateAtom) {
			boolean settingPositive = literal.getSign() == 1;
			EprGroundPredicateAtom egpa = (EprGroundPredicateAtom) literal.getAtom();
			TermTuple point = egpa.getArgumentsAsTermTuple(); 
			EprPredicate pred = egpa.eprPredicate; 

			HashSet<Literal> qo = pred.getQuantifiedOccurences().get(this);
			if (qo != null) {
				for (Literal quantifiedLit : qo) {
					boolean oppositeSigns = (quantifiedLit.getSign() == 1) ^ settingPositive;
					TermTuple otherPoint = new TermTuple(((EprPredicateAtom) quantifiedLit.getAtom()).getArguments());
					HashMap<TermVariable, Term> subs = point.match(otherPoint);
					if (oppositeSigns && subs != null) {
						setQuantifiedLiteralUnfulfillable(quantifiedLit, literal);
					}
				}
			}
		}	
	}


	/**
	 * Upgrade the clause state to account for the fact that the setting of literal has been reverted/backtracked.
	 * @param literal
	 */
	public void unsetGroundLiteral(Literal literal) {
		for (Literal li : groundLiterals) {
			if (literal.getAtom().equals(li.getAtom())) {
				if (literal.getSign() == li.getSign()) {
					assert mFulfillabilityStatus.get(li) == FulfillabilityStatus.Fulfilled;
					setLiteralFulfillable(li);
				} else {
					assert mFulfillabilityStatus.get(li) == FulfillabilityStatus.Unfulfillable;
					setLiteralFulfillable(li);
				}
			}
		}
		
		// deal with quantified literals that may have been made unfulfillable by the setting of literal
		//  revert their status if this was the only reason of unfulfillability
		for (Entry<Literal, HashSet<Literal>> en : mLiteralToUnfulfillabilityReasons.entrySet()) {
			boolean literalWasContained = en.getValue().remove(literal);
			if (literalWasContained 
					&& en.getValue().isEmpty()) {
				setLiteralFulfillable(en.getKey());
			}
		}
	}

	/**
	 * @return true if at least one of the literals of this clause is definitely true.
	 */
	public boolean isFulfilled() {
		return !mFulfilledLiterals.isEmpty();
	}

	/**
	 * Update the current solverstate wrt this clause according to the setting of qLiteral.
	 *  - If qLiteral occurs in this clause "as is" (i.e. only trivial unification is needed), 
	 *    this means that we can update the clause in-place, DPLL-style, i.e., update the
	 *    fulfillability-status of the literals, or the whole clause
	 *      (TODO: what if there is no unifier? what about factoring?)
	 *  - If the clause has a literal using the same eprPredicate as qLiteral 
	 *   -- .. and that has an opposite sign, we return a fresh clause that follows 
	 *     through first-order resolution with the unit-clause containing qLiteral
	 *   -- .. and that has the same sign, and qLiteral is more general than the literal
	 *      in this clause, we mark this literal as fulfilled.. (..?) 
	 *        (--> EprTheory will then mark the whole clause fulfilled)
	 *   -- .. and that has the same sign, and qLiteral is -not- more general than the 
	 *      literal in the clause, we do nothing
	 * @param qLiteral
	 * @return a fresh EprClause that follows from first-order resolution with qLiteral
	 */
	public EprClause setQuantifiedLiteral(EprQuantifiedLitWExcptns eqlwe) {
		boolean positive = eqlwe.mIsPositive;
		EprQuantifiedPredicateAtom atom = eqlwe.mAtom;
		HashMap<TermVariable, ArrayList<ApplicationTerm>> exceptions = eqlwe.mExceptedPoints;
		assert exceptions == null || exceptions.isEmpty() : "treat this case!";
		
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
//			HashMap<TermVariable, Term> sub = atomArgs.match(otherArgs);//TODO does not work this way, seems fishy..

			// if there is no unifier, do nothing
			if (sub == null)
				continue;
			
			// if the unifier is trivial, update this clauses' satisfiability status accordingly
			if (isUnifierTrivial(sub, atomArgs, otherArgs)) {
				
				// if the signs match, the clause is fulfilled
				if (positive == otherPositive
						&& otherIsQuantified) {
					setLiteralFulfillable(otherLit);
					assert !mFulfilledLiterals.contains(otherAtom);
					mFulfilledLiterals.add(otherLit);
				} else if (positive != otherPositive
						&& otherIsQuantified) {
					setLiteralUnfulfillable(otherLit);
					assert !mFulfilledLiterals.contains(otherAtom);
				} else if (positive == otherPositive
						&& !otherIsQuantified) {
					setGroundLiteral(otherLit);
				} else {
					setLiteralFulfillable(otherLit);
				}
			
				//TODO: deal with the case where several literals have the same predicate as qLiteral
				return null;
			} else {
				// if the unifier is non-trivial, create a new clause
				return instantiateClause(otherLit, sub);
			}
		}
		return null;
	}

	/**
	 * Create a new clause that is gained from applying the substitution sub to all literals in this clause.
	 * otherLit is omitted (typically because it is the pivot literal of a resolution).
	 * @param otherLit
	 * @param sub
	 * @return
	 */
	public EprClause instantiateClause(Literal otherLit, HashMap<TermVariable, Term> sub) {
		ArrayList<Literal> newLits = new ArrayList<Literal>();
		newLits.addAll(Arrays.asList(groundLiterals));
		for (Literal l : eprEqualityLiterals)
			newLits.add(applySubstitution(sub, l));
		for (Literal l : eprQuantifiedPredicateLiterals) {
			if (l.equals(otherLit))
				continue;
			newLits.add(applySubstitution(sub, l));
		}
		
		return new EprClause(newLits.toArray(new Literal[newLits.size()]), mTheory);
	}


	private Literal applySubstitution(HashMap<TermVariable, Term> sub, Literal l) {
		boolean isPositive = l.getSign() == 1;
		DPLLAtom atom = l.getAtom();
		
		if (atom instanceof EprQuantifiedPredicateAtom) {
			EprQuantifiedPredicateAtom eqpa = (EprQuantifiedPredicateAtom) atom;
			TermTuple newTT = eqpa.getArgumentsAsTermTuple().applySubstitution(sub);
			Term[] newParams = newTT.terms;
			ApplicationTerm newTerm = mTheory.term(eqpa.eprPredicate.functionSymbol, newParams);
			EprPredicateAtom result = null;
			if (newTerm.getFreeVars().length > 0) {
				result =  new EprQuantifiedPredicateAtom(newTerm, 0, //TODO: hash
						l.getAtom().getAssertionStackLevel(), 
						eqpa.eprPredicate);
			} else {
					EprGroundPredicateAtom pointAtom = eqpa.eprPredicate.getAtomForPoint(newTT);
					if (pointAtom != null) {
						result = pointAtom;
					} else {
						result = new EprGroundPredicateAtom(newTerm, 0, //TODO: hash
								l.getAtom().getAssertionStackLevel(), 
								eqpa.eprPredicate);
					}
			}
			return isPositive ? result : result.negate();
		} else {
			return l;
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

	/**
	 * 
	 */
	public void updateClauseState(EprStateManager mEprStateManager) {
		// TODO Auto-generated method stub
		
	}




}
