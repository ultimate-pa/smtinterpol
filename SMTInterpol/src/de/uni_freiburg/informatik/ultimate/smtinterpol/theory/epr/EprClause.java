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
public class EprClause extends Clause {
	
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
//	int mClauseIndex = 0;

//	private Literal mUnitLiteral;
	private UnFulReason mUnitLiteral;
	private EprClause mInstantiationOfClauseForCurrentUnitLiteral;

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
//	EprClause mExplanation = null;
	Object mExplanation = null;

	private HashMap<Literal, HashSet<UnFulReason>> mLiteralToUnfulfillabilityReasons = new HashMap<>();
	
	EprStateManager mStateManager;
	EqualityManager mEqualityManager;

	public EprClause(Literal[] literals, Theory theory, EprStateManager stateManager, Object explanation) {
		super(literals);
		theory = theory;
		mStateManager = stateManager;
		mEqualityManager = stateManager.mEqualityManager;
		mExplanation = explanation;
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
		
		// is this a unit clause upon creation?
		if (groundLiterals.length == 0
				&& eprQuantifiedPredicateLiterals.length == 1) {
			if (eprEqualityAtoms.length == 0) {
				mUnitLiteral = new UnFulReason(literals[0]);
			} else {
				Literal lit = eprQuantifiedPredicateLiterals[0];
				EprQuantifiedLitWExcptns eqlwe = EprHelpers.buildEQLWE(
						lit.getSign() == 1, 
						(EprQuantifiedPredicateAtom) lit.getAtom(), 
						eprEqualityAtoms, this,
						mTheory, mStateManager);
				mUnitLiteral = new UnFulReason(eqlwe);
			}
		} else if (groundLiterals.length == 1
				&& eprQuantifiedPredicateLiterals.length == 0) {
			if (eprEqualityAtoms.length == 0) {
				mUnitLiteral = new UnFulReason(groundLiterals[0]);
			} else {
				assert false : "quantified equalities but not quantified literals: "
						+ "this should have been caught before";
			}
			
		}
		
		//the equalities are handled separately
		mAllLiterals.removeAll(Arrays.asList(eprEqualityAtoms));

		// set fulfillability status
		mNoFulfillableLiterals = 0;

		setLiteralStates();
		
		if (mNoFulfillableLiterals == 1)
			searchUnitLiteral();
	}



	/**
	 * Helper for setting up the clause:
	 * Set the state of euch literal in this clause to fulfilled/fulfillable/unfulfillable
	 * according to the current state stored in the EprStatemanager.
	 */
	private void setLiteralStates() {
		nextLi:
		for (Literal li : eprQuantifiedPredicateLiterals) {

			boolean continueWithNextLiteral = compareToSetQuantifiedLiterals(li);
			if (continueWithNextLiteral)
				continue nextLi;

			EprQuantifiedPredicateAtom liAtom = (EprQuantifiedPredicateAtom) li.getAtom();
			boolean liPositive = li.getSign() == 1;
			// we only reach here if none of the quantified literals in the current state 
			//  fulfilled or contradicted li
			HashSet<TermTuple> otherPolarityPoints = mStateManager.getPoints(!liPositive, liAtom.eprPredicate);
			for (TermTuple opPoint : otherPolarityPoints) { // TODO: seems awfully inefficient..
				if (opPoint.match(liAtom.getArgumentsAsTermTuple(), mEqualityManager) != null) {
//				if (opPoint.match(liAtom.getArgumentsAsTermTuple()) != null) {
					EprGroundPredicateAtom opAtom = liAtom.eprPredicate.getAtomForPoint(opPoint);
					setLiteralUnfulfillable(li, new UnFulReason(liPositive ? opAtom.negate() : opAtom));
					continue nextLi;
				}
			}
			
			//TODO: can a quantifiedLiteral be fulfilled by enough points???
			// --> in principle yes .. depends on the model .. not sure .. do we need to account for that here?
			
			//if nothing said otherwise, li is fulfillable
			setLiteralFulfillable(li);
		}
		

		for (Literal li : groundLiterals) {
			DPLLAtom liAtom = li.getAtom();
			boolean liPositive = li.getSign() == 1;
			if (liAtom.getDecideStatus() == li) {
				setLiteralFulfilled(li);
			} else if (liAtom.getDecideStatus() == li.negate()) {
				setLiteralUnfulfillable(li, new UnFulReason(li));
			} else { //atom is undecided on the DPLL-side (maybe DPLLEngine does not know it??
				if (liAtom instanceof EprGroundPredicateAtom) {
					
					// compare to set quantified literals
					boolean continueWithNextLiteral = compareToSetQuantifiedLiterals(li);
					if (continueWithNextLiteral)
						continue;

					EprGroundPredicateAtom egpa = (EprGroundPredicateAtom) liAtom;
					// compare to points
					HashSet<TermTuple> samePolarityPoints = mStateManager.getPoints(liPositive, 
							egpa.eprPredicate);
					if (samePolarityPoints.contains(egpa.getArgumentsAsTermTuple())) {//TODO: seems inefficient..
//							assert false : "if this is reachable there are "
//									+ "ground atoms that are not known to DPLLEngine - "
//									+ "not necessarily bad, but good to know, maybe..";
							setLiteralFulfilled(li);
							continue;
					}
					HashSet<TermTuple> otherPolarityPoints = mStateManager.getPoints(liPositive, 
							((EprGroundPredicateAtom) liAtom).eprPredicate);
					if (otherPolarityPoints.contains(egpa.getArgumentsAsTermTuple())) {//TODO: seems inefficient..
//						assert false : "if this is reachable there are "
//									+ "ground atoms that are not known to DPLLEngine - "
//									+ "not necessarily bad, but good to know, maybe..";
					EprGroundPredicateAtom opAtom = ((EprGroundPredicateAtom) liAtom).
							eprPredicate.getAtomForPoint(
									egpa.getArgumentsAsTermTuple());
						setLiteralUnfulfillable(li, new UnFulReason(liPositive ? opAtom.negate() : opAtom));
						continue;
					}

				}
				setLiteralFulfillable(li);
			}
		}
		
//		for (Literal l : this.eprEqualityLiterals) {
//			setLiteralUnfulfillable(l, null); //"quantifed equality literal --> we don't track its fulfillability for itself, "
//					//+ "but through handling quantified epr predicate accordingly");
//		}
		
		assert this.getLiteralSet().containsAll(mFulfillabilityStatus.keySet())	&& 
		mFulfillabilityStatus.keySet().containsAll(this.getLiteralSet()) :
			"Fulfillability status map is incomplete.";
	}

	/**
	 * Given li, a quantified literal of this clause, which uses an uninterpreted predicate, 
	 * set the status of li to fulfilled/fulfillable/unfulfillable according to which 
	 * quantified literals are set in the current state (as known to the EprStateManager). 
	 * 
	 * If li conflicts with a set quantified literal, do resolution, and add the new clause
	 * to the derived clauses.
	 * 
	 * @param li the literal to set the status of
	 * @return true if the state of li was set because of, false if the quantified literals
	 *           in the current state are indifferent to li
	 */
	private boolean compareToSetQuantifiedLiterals(Literal li) {
		EprQuantifiedPredicateAtom liAtom = (EprQuantifiedPredicateAtom) li.getAtom();
		boolean liPositive = li.getSign() == 1;

		for (EprQuantifiedLitWExcptns sl : mStateManager.getSetLiterals(liAtom.eprPredicate)) {
			TermTuple liTT = liAtom.getArgumentsAsTermTuple();
			TermTuple slTT = sl.getPredicateAtom().getArgumentsAsTermTuple();
			TTSubstitution sub = liTT.match(slTT, mEqualityManager);
			if (sub == null)
				continue;
//			if (subset(sl.mExceptedPoints, this.mExceptedPoints)) { // is this an efficient solution? --> then mb bring it back some time
			
		
			if ((sl.getPredicateLiteral().getSign() == 1) == liPositive) {
				assert false : "TODO..";
			} else {
				EprQuantifiedLitWExcptns liEQLWE = 
					EprHelpers.buildEQLWE(liPositive, 
							liAtom, 
							eprEqualityAtoms, null, //explanation should not be used..
							mTheory, mStateManager);
				EprClause resolvent  = 
						sl.resolveAgainst(liEQLWE, sub, mTheory, 0); //TODO: set stacklevel
				
				if (resolvent.isTautology) {
					// the eqlwe don't affect each other --> do nothing 
				} else if (resolvent.isConflictClause()) {
					setLiteralUnfulfillable(li, new UnFulReason(sl));
				} else {
					ArrayList<Literal> eeas = new ArrayList<>();
					eeas.addAll(Arrays.asList(resolvent.eprEqualityAtoms));
					eeas.addAll(Arrays.asList(resolvent.groundLiterals));
					assert resolvent.eprQuantifiedPredicateLiterals.length == 0;
					assert resolvent.groundLiterals.length == 0
							|| resolvent.groundLiterals[0] instanceof CCEquality : 
								"the resolvent should only consist of equalities, right???";
					EprClause dc = this.instantiateClause(li, sub, eeas);
					mStateManager.addDerivedClause(dc);
				}
			}

//				if (sl.mIsPositive == liPositive) {
//					if (sub.isEmpty() || isUnifierJustARenaming(sub, liTT, slTT)) {
//						setLiteralFulfilled(li);
//						return true;
//					}
//				} else {
//					setLiteralUnfulfillable(li, new UnFulReason(sl));
//					if (!isUnifierJustARenaming(sub, liTT, slTT) && doesUnifierChangeTheClause(sub, this)) {
//						EprClause dc = instantiateClause(li, sub);
//						if (!dc.isTautology) {
//							System.out.println("EPRDEBUG (EprClause): " + sl + " is set. Creating clause " + this + 
//									". ==> adding derived clause " + this + "\\" + li + " with unifier " + sub);
//							mStateManager.addDerivedClause(dc); //resolution with the unit-clause {sl}
//						} else {
//							System.out.println("EPRDEBUG (EprClause): not adding tautology: " + dc);
//						}
//					}
//					return true;
//				}
//			}
		}
		return false;
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
	 * @return the only literal in the clause that is still fulfillable, null, if there is no such literal
	 */
	public UnFulReason getUnitClauseLiteral() {
		if (!mFulfilledLiterals.isEmpty()) {
			mInstantiationOfClauseForCurrentUnitLiteral = null;
			return null;
		}
		if (this.mUnitLiteral == null) {
			mInstantiationOfClauseForCurrentUnitLiteral = null;
			return null;
		}
		if (this.mUnitLiteral.mLiteral != null &&
				!(this.mUnitLiteral.mLiteral.getAtom() instanceof EprQuantifiedPredicateAtom)) {
			// unit literal is ground
			mInstantiationOfClauseForCurrentUnitLiteral = null;
			return mUnitLiteral;
		}
		
		//if the unitLiteral is a quantified literal, then we first have to find out if there is 
		// a unifier with the conflicts because of which we set the others "unfulfillable"
		// if not, we cannot do a unitpropagation
		ArrayDeque<HashSet<TermTuple>> conflictPointSets = new ArrayDeque<>();
		ArrayDeque<TermTuple> pointsFromLiterals = new ArrayDeque<>();

		for (Literal li : eprQuantifiedPredicateLiterals) {
			if (li.equals(mUnitLiteral.getLiteral()))
				continue;
			EprQuantifiedPredicateAtom liAtom = (EprQuantifiedPredicateAtom) li.getAtom();
			pointsFromLiterals.add(liAtom.getArgumentsAsTermTuple());
			conflictPointSets.add(new HashSet<TermTuple>());
			HashSet<UnFulReason> ur = mLiteralToUnfulfillabilityReasons.get(li);
			for (UnFulReason ufr : ur) {
				if (ufr.mLiteral != null)
					conflictPointSets.getLast().add(((EprGroundPredicateAtom) ufr.mLiteral.getAtom()).getArgumentsAsTermTuple());
				else {
					if (ufr.mqlwe.mExceptions.length == 0) {
						conflictPointSets.getLast().add(ufr.mqlwe.getPredicateAtom().getArgumentsAsTermTuple());
					} else {
						//TODO : probably we need to track, and later use the equalities 
						// that are created when resolving the literal with its UnFulReason
						assert false : "not yet implemented -- what to do with excepted points??";
					}
				}
			}
		}
		
		TTSubstitution sub = new ComputeInstantiations(conflictPointSets, pointsFromLiterals)
				.getSubstitution();

		if (sub == null) {
			mInstantiationOfClauseForCurrentUnitLiteral = null;
			return null; // if there is no unifier, then this clause actually is no unit clause
		}
		UnFulReason unifiedUnitLiteral = null;
		if (sub.isEmpty()) {  //TODO is emptiness enough to check?
//			unification is trivial, no need for a derived clause
			unifiedUnitLiteral = mUnitLiteral;
		} else {
			if (mUnitLiteral.mLiteral != null) {
				unifiedUnitLiteral = new UnFulReason(EprHelpers
						.applySubstitution(sub, mUnitLiteral.mLiteral, mTheory)); 
				 //TODO: register the new literal somewhere???
				
				if (mStateManager.isSubsumedInCurrentState(unifiedUnitLiteral.mLiteral)) { // already set??
					mUnitLiteral = null;
					return null; //TODO: seems incomplete, maybe we want to propagate other points, then..
				}
			} else {
				EprQuantifiedLitWExcptns rawUnitEqlwe = mUnitLiteral.mqlwe;
				

				Literal realLiteral = EprHelpers.applySubstitution(sub, 
						rawUnitEqlwe.getPredicateLiteral(), mTheory);
				EprPredicateAtom realAtom = (EprPredicateAtom) realLiteral.getAtom();

//				ArrayList<Literal> exceptions = new ArrayList<>();
//						Arrays.asList(eprEqualityAtoms)); 
				ArrayList<EprEqualityAtom> exceptions = new ArrayList<>();
				ArrayList<DPLLAtom> eqs = rawUnitEqlwe.substituteInExceptions(sub, mTheory);
				for (DPLLAtom eq : eqs) {
					if (eq instanceof EprEqualityAtom) {
						exceptions.add((EprEqualityAtom) eq);
					} else if (eq instanceof CCEquality) {
						assert false : "TODO: do";
					} else 
						assert false : "should not happen";
				}
				

				if (realAtom instanceof EprQuantifiedPredicateAtom) {
					EprQuantifiedLitWExcptns realUnitEqlwe = EprHelpers.buildEQLWE(
							realLiteral.getSign() == 1, 
							(EprQuantifiedPredicateAtom) realAtom, 
							exceptions.toArray(new EprEqualityAtom[exceptions.size()]), 
							this, mTheory, mStateManager);
					unifiedUnitLiteral = new UnFulReason(realUnitEqlwe);
				} else {
					unifiedUnitLiteral = new UnFulReason(realLiteral);
				}
				
			}
			mInstantiationOfClauseForCurrentUnitLiteral = this.instantiateClause(null, sub);
			mStateManager.addDerivedClause(mInstantiationOfClauseForCurrentUnitLiteral);
		}
		return unifiedUnitLiteral;
	}
	
	/**
	 * If this is a unit clause, then this yield the explanation clause, which is this clause instantiated in a way
	 *  such that it really is a unit clause 
	 *  (i.e. a ground unit clause or a set of such -- for a partial instantiation of the freevars..)
	 *  TODO: does not look so nice from the programming point of view..
	 * @return
	 */
	public EprClause getInstantiationOfClauseForCurrentUnitLiteral() {
		return mInstantiationOfClauseForCurrentUnitLiteral;
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
		
		mUnitLiteral = null;
		
		//TODO: this could be done more efficiently i guess..
		for (Literal li : eprQuantifiedPredicateLiterals) {
			if (mFulfillabilityStatus.get(li) == FulfillabilityStatus.Unfulfillable) {
				
			} else if (mFulfillabilityStatus.get(li) == FulfillabilityStatus.Fulfillable) {
				assert mUnitLiteral == null : "more than one literals are fulfillable -- something's wrong!";
				if (eprEqualityAtoms.length == 0) {
					mUnitLiteral = new UnFulReason(li);
				} else {
					if (li instanceof EprQuantifiedPredicateAtom) {
						mUnitLiteral = new UnFulReason(
								EprHelpers.buildEQLWE(li.getSign() == 1, 
								(EprQuantifiedPredicateAtom) li.getAtom(), eprEqualityAtoms, this,
								mTheory, mStateManager));
					} else {
						assert false : "TODO -- something about finite models";
					}
				}
			} else if (mFulfillabilityStatus.get(li) == FulfillabilityStatus.Fulfilled) {
				assert false : "the whole clause is fulfilled -- then why should this method be called??";
			} else 
				assert false : "li has no fulfillabilityStatus";
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
	
	private void setLiteralUnfulfillable(Literal li, UnFulReason reason) {
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
		
		HashSet<UnFulReason> ufr = mLiteralToUnfulfillabilityReasons.get(li);
		if (ufr == null) {
			ufr = new HashSet<>();
			mLiteralToUnfulfillabilityReasons.put(li, ufr);
		}
		ufr.add(reason);
	}
	
	public void setQuantifiedLiteralUnfulfillable(Literal quantifiedLit, Literal reason) {
		assert quantifiedLit.getAtom() instanceof EprQuantifiedPredicateAtom;
		setLiteralUnfulfillable(quantifiedLit, new UnFulReason(reason));
//		updateLiteralToUnfulfillabilityReasons(quantifiedLit, reason);
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
					setLiteralUnfulfillable(li, new UnFulReason(li)); //TODO: is this right? -- "li is its own reason, bc coming from setLiteral or so..
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
//					HashMap<TermVariable, Term> subs = point.match(otherPoint);
					TTSubstitution subs = point.match(otherPoint, mEqualityManager);
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
		for (Entry<Literal, HashSet<UnFulReason>> en : mLiteralToUnfulfillabilityReasons.entrySet()) {
//			boolean literalWasContained = false;
			UnFulReason match = null;
			for (UnFulReason ufr : en.getValue()) { //TODO not nice..
				if (ufr.mLiteral.equals(literal)) {
					match = ufr;
				}
			}
			en.getValue().remove(match);
//			if (literalWasContained 
			if (match != null 
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
	 * Update the current state of this clause's literals according to the setting of qLiteral.
	 * (difference to compareToSetQuantifiedLiterals: this is called when we freshly set a 
	 *   quantified literal, the other is called upon creation of the clause)
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
	public EprClause setQuantifiedLiteral(EprQuantifiedLitWExcptns setEqlwe) {
		boolean setLitPositive = setEqlwe.getPredicateLiteral().getSign() == 1;
		EprQuantifiedPredicateAtom setLitAtom = setEqlwe.getPredicateAtom();
//		HashMap<TermVariable, HashSet<ApplicationTerm>> exceptions = eqlwe.mExceptedPoints;
//		assert exceptions == null || exceptions.isEmpty() : "treat this case!";
		
		ArrayList<Literal> predicateLiterals = new ArrayList<>();
		predicateLiterals.addAll(Arrays.asList(eprQuantifiedPredicateLiterals));
		for (Literal l : groundLiterals) 
			if (l instanceof EprGroundPredicateAtom)
				predicateLiterals.add(l);
		
		for (Literal clauseLit : predicateLiterals) {
			boolean clauseLitPositive = clauseLit.getSign() == 1;
			EprPredicateAtom clauseLitAtom = (EprPredicateAtom) clauseLit.getAtom();
			boolean clauseLitIsQuantified = clauseLitAtom instanceof EprQuantifiedPredicateAtom;

			// do the eprPredicates match? do nothing if they don't
			if (!clauseLitAtom.eprPredicate.equals(setLitAtom.eprPredicate)) 
				continue;

			// is there a unifier?
			TermTuple atomArgs = setLitAtom.getArgumentsAsTermTuple();
			TermTuple otherArgs = clauseLitAtom.getArgumentsAsTermTuple();
			TTSubstitution sub = otherArgs.match(atomArgs, mEqualityManager);

			// if there is no unifier, do nothing
			if (sub == null)
				continue;

			if (clauseLitPositive == setLitPositive) {
				assert false : "TODO..";
			} else {
				EprClause resolvent  = null;
				if (clauseLitIsQuantified) {
					EprQuantifiedLitWExcptns liEQLWE = 
							EprHelpers.buildEQLWE(clauseLitPositive, (EprQuantifiedPredicateAtom) clauseLitAtom, 
									eprEqualityAtoms, null,//explanation should not be used..
									mTheory, mStateManager);
					resolvent  = 
							setEqlwe.resolveAgainst(liEQLWE, 
									sub, mTheory, 0); //TODO: set stacklevel
				} else {
						resolvent  = 
							setEqlwe.resolveAgainst(clauseLitAtom, sub, mTheory, 0);//TODO: set stacklevel
				}
				
				
				if (resolvent.isTautology) {
					// the eqlwe don't affect each other --> do nothing 
				} else if (resolvent.isConflictClause()) {
					setLiteralUnfulfillable(clauseLit, new UnFulReason(setEqlwe));
				} else {
					ArrayList<Literal> eeas = new ArrayList<>();
					eeas.addAll(Arrays.asList(resolvent.eprEqualityAtoms));
					EprClause dc = this.instantiateClause(clauseLit, sub, eeas);
					mStateManager.addDerivedClause(dc);
				}
			}
//			// if the unifier is trivial, update this clauses' satisfiability status accordingly
//			boolean unifierTrivial = isUnifierJustARenaming(sub, atomArgs, otherArgs);
//			if (unifierTrivial) {
//				
//				// if the signs match, the clause is fulfilled
//				if (positive == otherPositive
//						&& otherIsQuantified) {
//					setLiteralFulfillable(otherLit);
////					assert !mFulfilledLiterals.contains(otherAtom);
//					mFulfilledLiterals.add(otherLit);
//				} else if (positive != otherPositive
//						&& otherIsQuantified) {
//					setLiteralUnfulfillable(otherLit, new UnFulReason(positive ? atom : atom.negate()));
////					assert !mFulfilledLiterals.contains(otherAtom);
//				} else if (positive == otherPositive
//						&& !otherIsQuantified) {
//					setGroundLiteral(otherLit);
//				} else {
//					setLiteralFulfillable(otherLit);
//				}
//				//TODO: deal with the case where several literals have the same predicate as qLiteral (factoring, multiple resolutions, ..?)
//			}
//
//			//resolution is possible if the signs don't match
//			Literal  skippedLit = positive != otherPositive ? otherLit : null;
//			
//			// if the unifier is not trivial the new clause is different --> return it
//			if (!unifierTrivial || skippedLit != null) {
////				EprClause newClause = instantiateClause(skippedLit, sub);
//				EprClause newClause = instantiateClause(skippedLit, sub);
//				mStateManager.addDerivedClause(newClause);
//				return newClause;
//			}
//			
//			// if this became a conflict clause, we need to return it
//			if (this.isConflictClause()) {
//				return this;
//			}
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
		
		return mStateManager.getClause(new HashSet<Literal>(newLits), mTheory, this);
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
	
	class UnFulReason {

		public UnFulReason(Literal li) {
			assert !(li.getAtom() instanceof EprQuantifiedPredicateAtom) : 
				"probably better to use an eqlwe in this case";
			mLiteral = li;
			mqlwe = null;
		}

		public UnFulReason(EprQuantifiedLitWExcptns qlwe) {
			mLiteral = null;
			mqlwe = qlwe;
		}
		
		final Literal mLiteral;
		final EprQuantifiedLitWExcptns mqlwe;
		
		/**
		 * returns just the literal form this UnFulReason.
		 */
		public Literal getLiteral() {
			if (mLiteral != null)
				return mLiteral;
			else
				return mqlwe.getPredicateLiteral();
		}
		
		@Override
		public String toString() {
			return mLiteral == null ? mqlwe.toString() : mLiteral.toString();
		}
	}

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

	public boolean isConflictClause() {
		for (Entry<Literal, FulfillabilityStatus> en : mFulfillabilityStatus.entrySet())
			if (en.getValue() != FulfillabilityStatus.Unfulfillable)
				return false;
		return true;
	}
	
	public HashSet<Literal> getLiteralSet() {
		return mAllLiterals;
	}
}
