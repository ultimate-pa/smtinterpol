package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.io.ObjectInputStream.GetField;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprStateManager;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;

public abstract class EprNonUnitClause extends EprClause {

	private EprUnitClause mUnitLiteral;
	private EprNonUnitClause mInstantiationOfClauseForCurrentUnitLiteral;

	private int mNoFulfillableLiterals;

	HashSet<Literal> mFulfilledLiterals = new HashSet<Literal>();
	
	private HashMap<Literal, FulfillabilityStatus> mFulfillabilityStatus = new HashMap<Literal, FulfillabilityStatus>();

	private HashMap<Literal, HashSet<EprUnitClause>> mLiteralToUnfulfillabilityReasons = new HashMap<>();

	
	
	public EprNonUnitClause(Literal[] literals, Theory theory, 
			EprStateManager stateManager, boolean freshAlphaRenamed) {
		super(literals, theory, stateManager, freshAlphaRenamed);
		setUp();
	}
	
	private void setUp() {
		// is this a unit clause upon creation?
		if (groundLiterals.length == 0
				&& eprQuantifiedPredicateLiterals.length == 1) {
			Literal lit = eprQuantifiedPredicateLiterals[0];
			EprQuantifiedUnitClause eqlwe = EprHelpers.buildEQLWE(
					lit,
					eprQuantifiedEqualityAtoms, this,
					mTheory, mStateManager);
			mUnitLiteral = eqlwe;
		} else if (groundLiterals.length == 1
				&& eprQuantifiedPredicateLiterals.length == 0) {
			if (eprQuantifiedEqualityAtoms.length == 0) {
				mUnitLiteral = new EprGroundUnitClause(groundLiterals[0], 
						mTheory, mStateManager, this);
			} else {
				assert false : "quantified equalities but not quantified literals: "
						+ "this should have been caught before";
			}
		}
		
		// set fulfillability status
		mNoFulfillableLiterals = 0;

		setLiteralStates();
		
		if (mNoFulfillableLiterals == 1)
			searchUnitLiteral();

	}
	
	/**
	 * @return the only literal in the clause that is still fulfillable, null, if there is no such literal
	 */
	public EprUnitClause getUnitClauseLiteral() {
		if (!mFulfilledLiterals.isEmpty()) {
			mInstantiationOfClauseForCurrentUnitLiteral = null;
			return null;
		}
		if (this.mUnitLiteral == null) {
			mInstantiationOfClauseForCurrentUnitLiteral = null;
			return null;
		}
		if (this.mUnitLiteral instanceof EprGroundUnitClause) {	// unit literal is ground
			mInstantiationOfClauseForCurrentUnitLiteral = null;
			return mUnitLiteral;
		}
		
		//if the unitLiteral is a quantified literal, then we first have to find out if there is 
		// a unifier with the conflicts because of which we set the others "unfulfillable"
		// if not, we cannot do a unitpropagation
		ArrayDeque<HashSet<TermTuple>> conflictPointSets = new ArrayDeque<>();
		ArrayDeque<TermTuple> pointsFromLiterals = new ArrayDeque<>();
		EprQuantifiedUnitClause quantUnitLit = (EprQuantifiedUnitClause) mUnitLiteral;

		for (Literal li : eprQuantifiedPredicateLiterals) {
			if (li.equals(quantUnitLit.getPredicateLiteral()))
				continue;
			EprQuantifiedPredicateAtom liAtom = (EprQuantifiedPredicateAtom) li.getAtom();
			pointsFromLiterals.add(liAtom.getArgumentsAsTermTuple());
			conflictPointSets.add(new HashSet<TermTuple>());
			HashSet<EprUnitClause> ur = mLiteralToUnfulfillabilityReasons.get(li);
			for (EprUnitClause ufr : ur) {
				if (ufr instanceof EprGroundUnitClause) {
					EprGroundPredicateAtom ua  = 
							(EprGroundPredicateAtom) ((EprGroundUnitClause) ufr).getLiteral().getAtom();
					conflictPointSets.getLast().add(ua.getArgumentsAsTermTuple());
				} else {
					EprQuantifiedUnitClause eqlwe = (EprQuantifiedUnitClause) ufr;
					if (eqlwe.mExceptions.length == 0) {
						conflictPointSets.getLast().add(eqlwe.getPredicateAtom().getArgumentsAsTermTuple());
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
		EprUnitClause unifiedUnitLiteral = null;
		if (sub.isEmpty()) {  //TODO is emptiness enough to check?
//			unification is trivial, no need for a derived clause
			unifiedUnitLiteral = mUnitLiteral;
		} else {
			EprQuantifiedUnitClause rawUnitEqlwe = (EprQuantifiedUnitClause) mUnitLiteral;

			Literal realLiteral = EprHelpers.applySubstitution(sub, 
					rawUnitEqlwe.getPredicateLiteral(), mTheory);
			EprPredicateAtom realAtom = (EprPredicateAtom) realLiteral.getAtom();

			ArrayList<EprQuantifiedEqualityAtom> exceptions = new ArrayList<>();
			ArrayList<DPLLAtom> eqs = EprHelpers.substituteInExceptions(
					rawUnitEqlwe.eprQuantifiedEqualityAtoms, sub, mTheory);
			for (DPLLAtom eq : eqs) {
				if (eq instanceof EprQuantifiedEqualityAtom) {
					exceptions.add((EprQuantifiedEqualityAtom) eq);
				} else if (eq instanceof CCEquality) {
					assert false : "TODO: do";
				} else 
					assert false : "should not happen";
			}

			if (realAtom instanceof EprQuantifiedPredicateAtom) {
				EprQuantifiedUnitClause realUnitEqlwe = EprHelpers.buildEQLWE(
						realLiteral,
						exceptions.toArray(new EprQuantifiedEqualityAtom[exceptions.size()]), 
						this, mTheory, mStateManager);
				unifiedUnitLiteral = realUnitEqlwe;
			} else {

				unifiedUnitLiteral = new EprGroundUnitClause(realLiteral, 
						mTheory, mStateManager, null);
			}
			
//			already set??
			if (mStateManager.isSubsumedInCurrentState(unifiedUnitLiteral)) { 
					//TODO
					assert false : 
						"this needs more thought.. can we set the clause as fulfilled now??";
				//					TODO: seems incomplete, maybe we want to propagate other points, then..
					mUnitLiteral = null;
					return null; 
			}

			mInstantiationOfClauseForCurrentUnitLiteral = 
					(EprNonUnitClause) this.instantiateClause(null, sub);
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
				if (li instanceof EprQuantifiedPredicateAtom) {
					mUnitLiteral = 
							EprHelpers.buildEQLWE(li, eprQuantifiedEqualityAtoms, this,
									mTheory, mStateManager);
				} else {
					assert false : "TODO -- something about finite models";
				}
			} else if (mFulfillabilityStatus.get(li) == FulfillabilityStatus.Fulfilled) {
				assert false : "the whole clause is fulfilled -- then why should this method be called??";
			} else 
				assert false : "li has no fulfillabilityStatus";
		}
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
					EprGroundPredicateAtom opAtom = liAtom.eprPredicate.getAtomForPoint(opPoint);
					Literal opLit = liPositive ? opAtom.negate() : opAtom;
					setLiteralUnfulfillable(li, 
							new EprGroundUnitClause(opLit, mTheory, mStateManager, null));
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
				setLiteralUnfulfillable(li, 
						new EprGroundUnitClause(li, mTheory, mStateManager, null));
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
							setLiteralFulfilled(li);
							continue;
					}
					HashSet<TermTuple> otherPolarityPoints = mStateManager.getPoints(liPositive, 
							((EprGroundPredicateAtom) liAtom).eprPredicate);
					if (otherPolarityPoints.contains(egpa.getArgumentsAsTermTuple())) {//TODO: seems inefficient..
					EprGroundPredicateAtom opAtom = ((EprGroundPredicateAtom) liAtom).
							eprPredicate.getAtomForPoint(
									egpa.getArgumentsAsTermTuple());
					Literal opLit = liPositive ? opAtom.negate() : opAtom;
						setLiteralUnfulfillable(li, 
								new EprGroundUnitClause(opLit, mTheory, mStateManager, null));
						continue;
					}

				}
				setLiteralFulfillable(li);
			}
		}
		
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

		for (EprQuantifiedUnitClause sl : mStateManager.getSetLiterals(liAtom.eprPredicate)) {
			TermTuple liTT = liAtom.getArgumentsAsTermTuple();
			TermTuple slTT = sl.getPredicateAtom().getArgumentsAsTermTuple();
			TTSubstitution sub = liTT.match(slTT, mEqualityManager);
			if (sub == null)
				continue;
			
			applySetLiteralToClauseLiteral(li, sl, sub);
		}
		return false;
	}

	/**
	 * Assumes 
	 *  - setLiteral and clauseLit have different polarities
	 *  - setLiteral has (just) been set.
	 *  - clauseLit is a literal of this clause
	 *  - sub is the non-null most-general unifier of the two
	 * Does
	 *  - update the fulfillabilityStatus of clauseLit according to setLiteral being set
	 *  - introduce a derived clause consisting of equalities if it is a resolvent of 
	 *   the clause "setLiteral"  and {clauseLit, this.eprEqualityAtoms}
	 * @param clauseLit
	 * @param setLiteral
	 * @param sub
	 */
	private void applySetLiteralToClauseLiteral(Literal clauseLit, 
			EprUnitClause setLiteral, TTSubstitution sub) {

		Literal setLiteralPredicateLiteral = setLiteral instanceof EprQuantifiedUnitClause ?
				((EprQuantifiedUnitClause) setLiteral).getPredicateLiteral() : 
					((EprGroundUnitClause) setLiteral).getLiteral();
				
		assert mAllLiterals.contains(clauseLit);
		assert setLiteralPredicateLiteral.getAtom() instanceof EprPredicateAtom;
		assert clauseLit.getAtom() instanceof EprPredicateAtom;
		assert ((EprPredicateAtom) setLiteralPredicateLiteral.getAtom()).eprPredicate.equals(
				((EprPredicateAtom) clauseLit.getAtom()).eprPredicate);

		boolean polaritiesMatch = clauseLit.getSign() == setLiteralPredicateLiteral.getSign();

		if (polaritiesMatch) {
			// same polarity --> check for implication
			ImplicationStatus impStat = getImplicationStatus(sub, clauseLit, this.eprQuantifiedEqualityAtoms, 
					setLiteralPredicateLiteral, setLiteral.eprQuantifiedEqualityAtoms);
			assert false : "TODO";
//			if (subset(sl.mExceptedPoints, this.mExceptedPoints)) { // is this an efficient solution? --> then mb bring it back some time
		} else {
			GetResolventStatus grs = new GetResolventStatus(sub, 
					setLiteralPredicateLiteral,	setLiteral.eprQuantifiedEqualityAtoms,
					clauseLit, eprQuantifiedEqualityAtoms);
			switch (grs.getResolventStatus()) {
			case Conflict:
				setLiteralUnfulfillable(clauseLit, setLiteral);
				break;
			case ForcesFinite:
				assert false : "TODO";
			break;
			case Ground:
				//ArrayList<Literal> eeas = new ArrayList<>();
				//					eeas.addAll(Arrays.asList(resolvent.eprEqualityAtoms));
				//					eeas.addAll(Arrays.asList(resolvent.groundLiterals));
				//					assert resolvent.eprQuantifiedPredicateLiterals.length == 0;
				//					assert resolvent.groundLiterals.length == 0
				//							|| resolvent.groundLiterals[0] instanceof CCEquality : 
				//								"the resolvent should only consist of equalities, right???";
				//					EprNonUnitClause dc = (EprNonUnitClause) this.instantiateClause(li, sub, eeas);
				//					mStateManager.addDerivedClause(dc);
				assert false : "TODO (use the above..)";
			break;
			case Tautology:
				// literals don't interfere --> do nothing
				break;
			default:
				assert false : "missing case";
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
	
	private void setLiteralUnfulfillable(Literal li, EprUnitClause reason) {
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
		
		HashSet<EprUnitClause> ufr = mLiteralToUnfulfillabilityReasons.get(li);
		if (ufr == null) {
			ufr = new HashSet<>();
			mLiteralToUnfulfillabilityReasons.put(li, ufr);
		}
		ufr.add(reason);
	}
	
	/**
	 * Upgrade the clause state to account for the fact that literal has been set.
	 * @param setLiteral
	 */
	public void setGroundLiteral(Literal setLiteral) {
		for (Literal li : groundLiterals) {
			if (setLiteral.getAtom().equals(li.getAtom())) {
				if (setLiteral.getSign() == li.getSign()) {
					setLiteralFulfilled(li);
				} else {
//					TODO: is this right? -- "li is its own reason, bc coming from setLiteral or so..
					setLiteralUnfulfillable(li, new EprGroundUnitClause(li, mTheory, mStateManager, null));
				}
			}
		}
		
		if (setLiteral.getAtom() instanceof EprGroundPredicateAtom) {
			// we have an ground literal that uses an epr predicate
			boolean settingPositive = setLiteral.getSign() == 1;
			EprGroundPredicateAtom egpa = (EprGroundPredicateAtom) setLiteral.getAtom();
			TermTuple point = egpa.getArgumentsAsTermTuple(); 
			EprPredicate pred = egpa.eprPredicate; 

			HashSet<Literal> qo = pred.getQuantifiedOccurences().get(this);
			if (qo != null) {
				for (Literal quantifiedLit : qo) {
					boolean oppositeSigns = (quantifiedLit.getSign() == 1) ^ settingPositive;
					TermTuple otherPoint = new TermTuple(((EprPredicateAtom) quantifiedLit.getAtom()).getArguments());
					TTSubstitution subs = point.match(otherPoint, mEqualityManager);

					if (subs != null) {
						applySetLiteralToClauseLiteral(quantifiedLit, 
								new EprGroundUnitClause(setLiteral, mTheory, mStateManager, null), 
								subs);
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
		for (Entry<Literal, HashSet<EprUnitClause>> en : mLiteralToUnfulfillabilityReasons.entrySet()) {
			EprUnitClause match = null;
			for (EprUnitClause ufr : en.getValue()) { //TODO not nice..
				if (ufr instanceof EprGroundUnitClause 
						&& ((EprGroundUnitClause) ufr).getLiteral().equals(literal)) {
					match = ufr;
				}
			}
			en.getValue().remove(match);
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
	public EprClause setQuantifiedLiteral(EprQuantifiedUnitClause setEqlwe) {
		EprQuantifiedPredicateAtom setLitAtom = setEqlwe.getPredicateAtom();
		
		ArrayList<Literal> predicateLiterals = new ArrayList<>();
		predicateLiterals.addAll(Arrays.asList(eprQuantifiedPredicateLiterals));
		for (Literal l : groundLiterals) 
			if (l instanceof EprGroundPredicateAtom)
				predicateLiterals.add(l);
		
		for (Literal clauseLit : predicateLiterals) {
			EprPredicateAtom clauseLitAtom = (EprPredicateAtom) clauseLit.getAtom();

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

			
			applySetLiteralToClauseLiteral(clauseLit, setEqlwe, sub);
		}
		return null;
	}


	
	public ImplicationStatus getImplicationStatus(TTSubstitution sub, Literal litA,
			EprQuantifiedEqualityAtom[] equalitiesA, Literal litB, EprQuantifiedEqualityAtom[] equalitiesB) {
		assert litA.getSign() == litB.getSign();
		assert litA.getAtom() instanceof EprPredicateAtom;
		assert litB.getAtom() instanceof EprPredicateAtom;
		assert ((EprPredicateAtom) litA.getAtom()).eprPredicate.equals(
				((EprPredicateAtom) litB.getAtom()).eprPredicate);
		
		ArrayList<DPLLAtom> unifiedEqualitiesA = EprHelpers.substituteInExceptions(
				equalitiesA, sub, mTheory);
		ArrayList<DPLLAtom> unifiedEqualitiesB = EprHelpers.substituteInExceptions(
				equalitiesB, sub, mTheory);
		
		ArrayList<EprGroundEqualityAtom> unifiedGroundEqualitiesA = 
				new ArrayList<>();
		ArrayList<EprGroundEqualityAtom> unifiedGroundEqualitiesB = 
				new ArrayList<>();
		// singly quantified equality means: (= x a) or so --> i.e. only one term
		//   of the two is a variable
		// doubly quantified is like (= x y)
		ArrayList<EprQuantifiedEqualityAtom> unifiedSinglyQuantifiedEqualitiesA = 
				new ArrayList<>();
		ArrayList<EprQuantifiedEqualityAtom> unifiedSinglyQuantifiedEqualitiesB = 
				new ArrayList<>();
		HashMap<TermVariable, HashSet<ApplicationTerm>> unifiedSinglyQuantifiedEqualitiesAasMap =
				new HashMap<>();
		HashMap<TermVariable, HashSet<ApplicationTerm>> unifiedSinglyQuantifiedEqualitiesBasMap =
				new HashMap<>();
		ArrayList<EprQuantifiedEqualityAtom> unifiedDoublyQuantifiedEqualitiesA = 
				new ArrayList<>();
		ArrayList<EprQuantifiedEqualityAtom> unifiedDoublyQuantifiedEqualitiesB = 
				new ArrayList<>();

		sortEqualities(unifiedEqualitiesA, 
				unifiedGroundEqualitiesA, 
				unifiedSinglyQuantifiedEqualitiesA, 
				unifiedSinglyQuantifiedEqualitiesAasMap,
				unifiedDoublyQuantifiedEqualitiesA);
		sortEqualities(unifiedEqualitiesB, 
				unifiedGroundEqualitiesB, 
				unifiedSinglyQuantifiedEqualitiesB, 
				unifiedSinglyQuantifiedEqualitiesBasMap,
				unifiedDoublyQuantifiedEqualitiesB);



		
		
		
		
		return null;
	}

	private void sortEqualities(ArrayList<DPLLAtom> unsortedEqualities,
			ArrayList<EprGroundEqualityAtom> groundEqualities,
			ArrayList<EprQuantifiedEqualityAtom> singlyQuantifiedEqualities,
			HashMap<TermVariable, HashSet<ApplicationTerm>> singlyQuantifiedEqualitiesAsMap,
			ArrayList<EprQuantifiedEqualityAtom> doublyQuantifiedEqualities) {
		for (DPLLAtom eq : unsortedEqualities) {
			if (eq instanceof EprGroundEqualityAtom) {
				groundEqualities.add((EprGroundEqualityAtom) eq);
			} else {
				EprQuantifiedEqualityAtom qea = (EprQuantifiedEqualityAtom) eq;
				if (qea.areBothQuantified()) {
					doublyQuantifiedEqualities.add(qea);
				} else {
					singlyQuantifiedEqualities.add(qea);

					// update map
					TermVariable tv = qea.getLhs() instanceof TermVariable ?
							(TermVariable) qea.getLhs() : (TermVariable) qea.getRhs();
					ApplicationTerm at = qea.getLhs() instanceof TermVariable ?
							(ApplicationTerm) qea.getRhs() : (ApplicationTerm) qea.getLhs();

					HashSet<ApplicationTerm> hs = singlyQuantifiedEqualitiesAsMap.get(tv);
					if (hs == null) {
						hs = new HashSet<>();
						singlyQuantifiedEqualitiesAsMap.put(tv, hs);
					}
					hs.add(at);
				}
			}
		}
	}

	public boolean isConflictClause() {
		for (Entry<Literal, FulfillabilityStatus> en : mFulfillabilityStatus.entrySet())
			if (en.getValue() != FulfillabilityStatus.Unfulfillable)
				return false;
		return true;
	}
	
	enum ResolventStatus {
		Tautology, Conflict, ForcesFinite, Ground
	}

	enum ImplicationStatus {
		AImpliesB, BImpliesA, Equivalent, Independent
	}
	
	class GetResolventStatus {
		ResolventStatus rs;
		EprClause resolvent;

		GetResolventStatus(TTSubstitution subs, Literal lit1, EprQuantifiedEqualityAtom[] eqAtoms1,
				Literal lit2, EprQuantifiedEqualityAtom[] eqAtoms2) {
			assert lit1.getSign() != lit2.getSign();
			assert lit1.getAtom() instanceof EprPredicateAtom;
			assert lit2.getAtom() instanceof EprPredicateAtom;

			EprQuantifiedEqualityAtom[] eq1 = lit1.getAtom() instanceof EprQuantifiedPredicateAtom ? 
					eqAtoms1 : new EprQuantifiedEqualityAtom[0];
			EprQuantifiedEqualityAtom[] eq2 = lit2.getAtom() instanceof EprQuantifiedPredicateAtom ? 
					eqAtoms2 : new EprQuantifiedEqualityAtom[0];


			Literal[] substEqualities = EprHelpers.applyUnifierToEqualities(
					eq1, eq2, subs, mTheory);										
			resolvent = 
					new EprDerivedClause(substEqualities, mTheory, mStateManager, this);

			if (resolvent.isTautology())
				rs = ResolventStatus.Tautology;
			else if (resolvent.isConflictClause())
				rs = ResolventStatus.Conflict;
			else if (resolvent.forcesFiniteModel)
				rs = ResolventStatus.ForcesFinite;
			else if (resolvent.isGround())
				rs = ResolventStatus.Ground;
			else
				assert false : "unforseen case.. -- what now?";
		}
		
		ResolventStatus getResolventStatus() {
			return rs;
		}
		
		EprClause getResolvent() {
			return resolvent;
		}
	}

	@Override
	public EprClause getAlphaRenamedVersion() {
		ArrayList<Literal> newLits = getFreshAlphaRenamedLiterals();

		if (this instanceof EprBaseClause) {
			return new EprBaseClause(newLits.toArray(new Literal[newLits.size()]), 
					mTheory, mStateManager, true);
		} else {
			assert this instanceof EprDerivedClause;
			return new EprDerivedClause(newLits.toArray(new Literal[newLits.size()]), 
					mTheory, mStateManager, true);
		}
	}

	public ArrayList<Literal> getFreshAlphaRenamedLiterals() {
		TTSubstitution sub = new TTSubstitution();
		for (TermVariable fv : this.getFreeVars()) {
			sub.addSubs(mTheory.createFreshTermVariable(fv.getName(), fv.getSort()), fv);
		}
		
		ArrayList<Literal> newLits = getSubstitutedLiterals(sub);
		return newLits;
	}
}
