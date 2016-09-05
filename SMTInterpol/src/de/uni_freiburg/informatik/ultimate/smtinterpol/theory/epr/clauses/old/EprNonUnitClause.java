package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.EprStateManager;

public abstract class EprNonUnitClause extends EprClauseOld {

	/**
	 * All constants (0-ary ApplicationTerms) that appear in a literal of this clause.
	 */
	private HashSet<ApplicationTerm> mAppearingConstants = new HashSet<ApplicationTerm>();


	private EprUnitClause mUnitLiteral;
	private HashMap<EprUnitClause, EprNonUnitClause> mUnitLiteralToInstantiationOfClause =
			new HashMap<EprUnitClause, EprNonUnitClause>();

	private int mNoFulfillableLiterals;

	HashSet<Literal> mFulfilledLiterals = new HashSet<Literal>();
	
	private HashMap<Literal, FulfillabilityStatus> mFulfillabilityStatus = new HashMap<Literal, FulfillabilityStatus>();

	private HashMap<Literal, HashSet<EprUnitClause>> mLiteralToUnfulfillabilityReasons = new HashMap<Literal, HashSet<EprUnitClause>>();

	private final EprNonUnitClause mClauseThisIsAFreshAlphaRenamingOf;
	
	public EprNonUnitClause(Literal[] literals, EprTheory eprTheory, 
			boolean freshAlphaRenamed, TTSubstitution freshAlphaRen, EprNonUnitClause clauseThisIsAFreshAlphaRenamingOf) {
		super(literals, eprTheory, freshAlphaRenamed, freshAlphaRen);
		assert !freshAlphaRenamed || freshAlphaRen != null;
		mClauseThisIsAFreshAlphaRenamingOf = clauseThisIsAFreshAlphaRenamingOf;
		setUp();
		
		mAppearingConstants = 
				EprHelpers.collectAppearingConstants(literals, mTheory);
	}
	
	private void setUp() {
		// is this a unit clause upon creation?
		if (groundLiterals.length == 0
				&& eprQuantifiedPredicateLiterals.length == 1) {
			Literal lit = eprQuantifiedPredicateLiterals[0];
			EprQuantifiedUnitClause eqlwe = EprHelpers.buildEQLWE(
					lit,
					eprQuantifiedEqualityAtoms, this,
					mEprTheory);
			mUnitLiteral = eqlwe;
		} else if (groundLiterals.length == 1
				&& eprQuantifiedPredicateLiterals.length == 0) {
			if (eprQuantifiedEqualityAtoms.length == 0) {
				mUnitLiteral = new EprGroundUnitClause(groundLiterals[0], 
						mEprTheory, this);
			} else {
				assert false : "quantified equalities but not quantified literals: "
						+ "this should have been caught before";
			}
		}
		
		// set fulfillability status
		mNoFulfillableLiterals = 0;

		if (isFreshAlphaRenamed) {
			// do nothing -- fulfillability is not needed in this case, right??
//			transferFulfillabilityInfo();
		} else {
			setLiteralStates();
		}
		
		if (mNoFulfillableLiterals == 1)
			searchUnitLiteral();

		
	}



	public void transferFulfillabilityInfo() {
		//TODO (if necessary): complete for other fields that are related to fulfillability information
		
		// transfer the literalStates of the clause this clause is an alpha renaming of to this clause
		// (instead of computing the from scratch
		HashMap<Literal, FulfillabilityStatus> oldFulfillability = mClauseThisIsAFreshAlphaRenamingOf.mFulfillabilityStatus;
		for (Literal oldClauseQl : mClauseThisIsAFreshAlphaRenamingOf.eprQuantifiedPredicateLiterals) {
			EprQuantifiedPredicateAtom oldClauseAtom = (EprQuantifiedPredicateAtom) oldClauseQl.getAtom();
			EprQuantifiedPredicateAtom atomInNewClause = 
					(EprQuantifiedPredicateAtom) oldClauseAtom.getEprPredicate().getAtomForTermTuple(
					mFreshAlphaRenaming.apply(
							oldClauseAtom.getArgumentsAsTermTuple()), mTheory, 0); //TODO assertionStackLevel
			Literal litInNewClause = oldClauseQl.getSign() == 1 ? atomInNewClause : atomInNewClause.negate();
			
			mFulfillabilityStatus.put(litInNewClause, oldFulfillability.get(oldClauseQl));
		}
		for (Literal oldClauseGl : mClauseThisIsAFreshAlphaRenamingOf.groundLiterals) {
			mFulfillabilityStatus.put(oldClauseGl, oldFulfillability.get(oldClauseGl));
		}
	}
	
	public boolean isConflictClause() {
		assert !isFreshAlphaRenamed;
		for (Entry<Literal, FulfillabilityStatus> en : mFulfillabilityStatus.entrySet())
			if (en.getValue() != FulfillabilityStatus.Unfulfillable)
				return false;
		
		ComputeClauseUnifiers ccu = new ComputeClauseUnifiers(
				new ArrayList<Literal>(Arrays.asList(eprQuantifiedPredicateLiterals)),
				mLiteralToUnfulfillabilityReasons, 
				eprQuantifiedEqualityAtoms);
		
		if (ccu.getSubstitutions().isEmpty()) {
			assert false: "should we do something here? Or just wait for model completion??";
			return false;
		}
		//TODO: save the computed substitutions somewhere?
		return true;
	}

	/**
	 * @return the only literal in the clause that is still fulfillable, null, if there is no such literal
	 */
	public EprUnitClause getUnitClauseLiteral() {
		if (!mFulfilledLiterals.isEmpty()) {
			mUnitLiteralToInstantiationOfClause.clear();
			return null;
		}
		if (this.mUnitLiteral == null) {
			mUnitLiteralToInstantiationOfClause.clear();
			return null;
		}
		if (this.mUnitLiteral instanceof EprGroundUnitClause) {	// unit literal is ground
			mUnitLiteralToInstantiationOfClause.clear();
			return mUnitLiteral;
		}
		
		assert mUnitLiteral instanceof EprQuantifiedUnitClause : "missed a case";
		//if the unitLiteral is a quantified literal, then we first have to find out if there is 
		// a unifier with the conflicts because of which we set the others "unfulfillable"
		// if not, we cannot do a unitpropagation
		// TODO: we probably need a kind of caching for this complex part --> otherwise it might get done often, 
		//  even when the state has not changed, right??
		ArrayList<Literal> eprQuantifiedPredicateLiteralsExceptUnitLiteral = 
				new ArrayList<Literal>(Arrays.asList(eprQuantifiedPredicateLiterals));
		eprQuantifiedPredicateLiteralsExceptUnitLiteral.remove(mUnitLiteral);
		

		ComputeClauseUnifiers ci = new ComputeClauseUnifiers(
				eprQuantifiedPredicateLiteralsExceptUnitLiteral,
				mLiteralToUnfulfillabilityReasons,
				eprQuantifiedEqualityAtoms);

		if (ci.getSubstitutions().isEmpty()) {
			mUnitLiteralToInstantiationOfClause = null;
			return null; // if there is no unifier, then this clause actually is no unit clause
		}
		
		HashSet<EprUnitClause> unifiedUnitLiterals = new HashSet<EprUnitClause>();
		
		for (TTSubstitution sub : ci.getSubstitutions()) {

			if (sub.isEmpty()) {  //TODO is emptiness enough to check?
				//			unification is trivial, no need for a derived clause
				unifiedUnitLiterals.add(mUnitLiteral);
				continue;
			} 

			EprQuantifiedUnitClause rawUnitEqlwe = (EprQuantifiedUnitClause) mUnitLiteral;

			Literal realLiteral = EprHelpers.applySubstitution(sub, 
					rawUnitEqlwe.getPredicateLiteral(), mEprTheory);
			EprPredicateAtom realAtom = (EprPredicateAtom) realLiteral.getAtom();

			// compute the substituted exceptions for the unit clause
			// note that none of these should become "true"/valid 
			//  -- computation of the substitutions already takes the exceptions into account for that very reason
			ArrayList<EprQuantifiedEqualityAtom> exceptions = new ArrayList<EprQuantifiedEqualityAtom>();
			ArrayList<DPLLAtom> eqs = EprHelpers.substituteInExceptions(
					rawUnitEqlwe.eprQuantifiedEqualityAtoms, sub, mEprTheory);
			for (DPLLAtom eq : eqs) {
				if (eq instanceof EprQuantifiedEqualityAtom) {
					exceptions.add((EprQuantifiedEqualityAtom) eq);
				} else if (eq instanceof CCEquality) {
					assert false : "TODO: do";
				} else 
					assert false : "should not happen";
			}

			EprUnitClause unifiedUnitLiteral;
			if (realAtom instanceof EprQuantifiedPredicateAtom) {
				EprQuantifiedUnitClause realUnitEqlwe = EprHelpers.buildEQLWE(
						realLiteral,
						exceptions.toArray(new EprQuantifiedEqualityAtom[exceptions.size()]), 
						this, mEprTheory);
				assert !realUnitEqlwe.isTautology() : "probably there's a bug in the exception handling "
						+ "of the computation of the substitutions (see above..)";
				unifiedUnitLiteral = realUnitEqlwe;
			} else {
				unifiedUnitLiteral = new EprGroundUnitClause(realLiteral, 
						mEprTheory, null);
			}

			//			already set??
			if (mStateManager.isSubsumedInCurrentState(unifiedUnitLiteral))
				continue;

			unifiedUnitLiterals.add(unifiedUnitLiteral);
			// TODO: alternatively we could just remember the substitution for each unit literal here 
			//   --> this here seems a bit "eager"..
			EprNonUnitClause instantiationOfClause = (EprNonUnitClause) this.instantiateClause(null, sub);
			mUnitLiteralToInstantiationOfClause.put(unifiedUnitLiteral, instantiationOfClause);
			// TODO: also: do we need to add the derived clause?? now??
			mStateManager.addDerivedClause(instantiationOfClause);
		}

		if (unifiedUnitLiterals.isEmpty())
			return null;
		else
			return unifiedUnitLiterals.iterator().next();
	}


	
	/**
	 * If this is a unit clause, then this yield the explanation clause, which is this clause instantiated in a way
	 *  such that it really is a unit clause 
	 *  (i.e. a ground unit clause or a set of such -- for a partial instantiation of the freevars..)
	 *  TODO: does not look so nice from the programming point of view..
	 * @return
	 */
	public EprClauseOld getInstantiationOfClauseForCurrentUnitLiteral(EprUnitClause uc) {
		return mUnitLiteralToInstantiationOfClause.get(uc);
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
				if (li.getAtom() instanceof EprQuantifiedPredicateAtom) {
					mUnitLiteral = 
							EprHelpers.buildEQLWE(li, eprQuantifiedEqualityAtoms, this,
									mEprTheory);
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
			HashSet<TermTuple> otherPolarityPoints = mStateManager.getPoints(!liPositive, liAtom.getEprPredicate());
			for (TermTuple opPoint : otherPolarityPoints) { // TODO: seems awfully inefficient..
				if (opPoint.match(liAtom.getArgumentsAsTermTuple(), mEqualityManager) != null) {
					EprGroundPredicateAtom opAtom = liAtom.getEprPredicate().getAtomForPoint(opPoint);
					Literal opLit = liPositive ? opAtom.negate() : opAtom;
					setLiteralUnfulfillable(li, 
							new EprGroundUnitClause(opLit, mEprTheory, null));
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
						new EprGroundUnitClause(li, mEprTheory, null));
			} else { //atom is undecided on the DPLL-side (maybe DPLLEngine does not know it??
				if (liAtom instanceof EprGroundPredicateAtom) {
					
					// compare to set quantified literals
					boolean continueWithNextLiteral = compareToSetQuantifiedLiterals(li);
					if (continueWithNextLiteral)
						continue;

					EprGroundPredicateAtom egpa = (EprGroundPredicateAtom) liAtom;
					// compare to points
					HashSet<TermTuple> samePolarityPoints = mStateManager.getPoints(liPositive, 
							egpa.getEprPredicate());
					if (samePolarityPoints.contains(egpa.getArgumentsAsTermTuple())) {//TODO: seems inefficient..
							setLiteralFulfilled(li);
							continue;
					}
					HashSet<TermTuple> otherPolarityPoints = mStateManager.getPoints(liPositive, 
							((EprGroundPredicateAtom) liAtom).getEprPredicate());
					if (otherPolarityPoints.contains(egpa.getArgumentsAsTermTuple())) {//TODO: seems inefficient..
					EprGroundPredicateAtom opAtom = ((EprGroundPredicateAtom) liAtom).
							getEprPredicate().getAtomForPoint(
									egpa.getArgumentsAsTermTuple());
					Literal opLit = liPositive ? opAtom.negate() : opAtom;
						setLiteralUnfulfillable(li, 
								new EprGroundUnitClause(opLit, mEprTheory, null));
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

		for (EprQuantifiedUnitClause slRaw : mStateManager.getSetLiterals(liAtom.getEprPredicate())) {
			EprQuantifiedUnitClause sl = slRaw.getFreshAlphaRenamedVersion();
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
	 *  - clauseLit is a literal over an EprPredicate
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
					((EprGroundUnitClause) setLiteral).getPredicateLiteral();
				
		assert mAllLiterals.contains(clauseLit);
		assert setLiteralPredicateLiteral.getAtom() instanceof EprPredicateAtom;
		assert clauseLit.getAtom() instanceof EprPredicateAtom;
		assert ((EprPredicateAtom) setLiteralPredicateLiteral.getAtom()).getEprPredicate().equals(
				((EprPredicateAtom) clauseLit.getAtom()).getEprPredicate());

		boolean polaritiesMatch = clauseLit.getSign() == setLiteralPredicateLiteral.getSign();

		if (polaritiesMatch) {
			// same polarity --> check for implication
//			ImplicationStatus impStat = checkImplication(sub, clauseLit, this.eprQuantifiedEqualityAtoms, 
			boolean setLitImpliesClauseLit = checkImplication(sub,  
					setLiteralPredicateLiteral, setLiteral.eprQuantifiedEqualityAtoms, 
					clauseLit, this.eprQuantifiedEqualityAtoms);
			if (setLitImpliesClauseLit) {
				setLiteralFulfilled(clauseLit);
			}
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
			ufr = new HashSet<EprUnitClause>();
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
			
			TTSubstitution sub = matchGroundAtoms(setLiteral.getAtom(), li.getAtom());
			if (sub == null) 
				continue;

			if (setLiteral.getSign() == li.getSign()) {
				setLiteralFulfilled(li);
			} else {
				//					TODO: is this right? -- "li is its own reason, bc coming from setLiteral or so..
				setLiteralUnfulfillable(li, new EprGroundUnitClause(setLiteral, mEprTheory, null));
			}
		}
		
		if (setLiteral.getAtom() instanceof EprGroundPredicateAtom) {
			// we have an ground literal that uses an epr predicate
			EprGroundPredicateAtom egpa = (EprGroundPredicateAtom) setLiteral.getAtom();
			TermTuple point = egpa.getArgumentsAsTermTuple(); 
			EprPredicate pred = egpa.getEprPredicate(); 

			HashSet<Literal> qo = null;//changed EprPredicate, old code: pred.getQuantifiedOccurences().get(this);
			if (qo != null) {
				for (Literal quantifiedLit : qo) {
					TermTuple otherPoint = new TermTuple(
							((EprPredicateAtom) quantifiedLit.getAtom()).getArguments());
					TTSubstitution subs = point.match(otherPoint, mEqualityManager);

					if (subs != null) {
						applySetLiteralToClauseLiteral(quantifiedLit, 
								new EprGroundUnitClause(setLiteral, mEprTheory, null), 
								subs);
					}
				}
			}
		}	
	}
	
	/**
	 * Checks if atom1 and atom2 match.
	 * Two ground atoms match if one of the following holds
	 *  - they are syntactically equal
	 *  - they share the same predicate symbol, and the equalities that hold in the current state
	 *    allow for unification of their arguments
	 * @param atom
	 * @param atom2
	 * @return null if atom1 and atom2 don't match, a (possibly empty) substitution otherwise
	 */
	private TTSubstitution matchGroundAtoms(DPLLAtom atom1, DPLLAtom atom2) {
		if (atom1.equals(atom2))
			return new TTSubstitution();

		ApplicationTerm term1 = (ApplicationTerm) atom1.getSMTFormula(mTheory);
		ApplicationTerm term2 = (ApplicationTerm) atom2.getSMTFormula(mTheory);
		if (!term1.getFunction().equals(term2.getFunction()))
			return null;
		
		TermTuple tt1 = new TermTuple(term1.getParameters());
		TermTuple tt2 = new TermTuple(term2.getParameters());
		
		return tt1.match(tt2, mEqualityManager);
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
						&& ((EprGroundUnitClause) ufr).getPredicateLiteral().equals(literal)) {
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
		assert !isFreshAlphaRenamed;
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
	public EprClauseOld setQuantifiedLiteral(EprQuantifiedUnitClause setEqlweRaw) {
	 	EprQuantifiedUnitClause setEqlwe = setEqlweRaw.getFreshAlphaRenamedVersion();
		EprQuantifiedPredicateAtom setLitAtom = setEqlwe.getPredicateAtom();
		
		ArrayList<Literal> predicateLiterals = new ArrayList<Literal>();
		predicateLiterals.addAll(Arrays.asList(eprQuantifiedPredicateLiterals));
		for (Literal l : groundLiterals) 
			if (l instanceof EprGroundPredicateAtom)
				predicateLiterals.add(l);
		
		for (Literal clauseLit : predicateLiterals) {
			EprPredicateAtom clauseLitAtom = (EprPredicateAtom) clauseLit.getAtom();

			// do the eprPredicates match? do nothing if they don't
			if (!clauseLitAtom.getEprPredicate().equals(setLitAtom.getEprPredicate())) 
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


	
	/**
	 * Answers the question if the following implication holds
	 *  sub({litA , equalitiesA}) -?-> sub({litB, equalitiesB})
	 * @param sub
	 * @param litA
	 * @param equalitiesA
	 * @param litB
	 * @param equalitiesB
	 * @return
	 */
//	public ImplicationStatus getImplicationStatus(TTSubstitution sub, Literal litA,
	public boolean checkImplication(TTSubstitution sub, Literal litA,
			EprQuantifiedEqualityAtom[] equalitiesA, Literal litB, EprQuantifiedEqualityAtom[] equalitiesB) {
		assert litA.getSign() == litB.getSign();
		assert litA.getAtom() instanceof EprPredicateAtom;
		assert litB.getAtom() instanceof EprPredicateAtom;
		assert ((EprPredicateAtom) litA.getAtom()).getEprPredicate().equals(
				((EprPredicateAtom) litB.getAtom()).getEprPredicate());
		
		///// check if the predicate atoms allow/deny implication
		boolean doesSpecializeAPred = doesUnifierSpecialize(sub, litA);
		boolean doesSpecializeBPred = doesUnifierSpecialize(sub, litB);
		
		if (doesSpecializeBPred)
			return false;
		
		
		///// check if the equalities allow/deny implication
		ArrayList<DPLLAtom> unifiedEqualitiesA = EprHelpers.substituteInExceptions(
				equalitiesA, sub, mEprTheory);
		ArrayList<DPLLAtom> unifiedEqualitiesB = EprHelpers.substituteInExceptions(
				equalitiesB, sub, mEprTheory);
		
		ArrayList<EprGroundEqualityAtom> unifiedGroundEqualitiesA = 
				new ArrayList<EprGroundEqualityAtom>();
		ArrayList<EprGroundEqualityAtom> unifiedGroundEqualitiesB = 
				new ArrayList<EprGroundEqualityAtom>();
		// singly quantified equality means: (= x a) or so --> i.e. only one term
		//   of the two is a variable
		// doubly quantified is like (= x y)
		ArrayList<EprQuantifiedEqualityAtom> unifiedSinglyQuantifiedEqualitiesA = 
				new ArrayList<EprQuantifiedEqualityAtom>();
		ArrayList<EprQuantifiedEqualityAtom> unifiedSinglyQuantifiedEqualitiesB = 
				new ArrayList<EprQuantifiedEqualityAtom>();
		HashMap<TermVariable, HashSet<ApplicationTerm>> unifiedSinglyQuantifiedEqualitiesAasMap =
				new HashMap<TermVariable, HashSet<ApplicationTerm>>();
		HashMap<TermVariable, HashSet<ApplicationTerm>> unifiedSinglyQuantifiedEqualitiesBasMap =
				new HashMap<TermVariable, HashSet<ApplicationTerm>>();
		ArrayList<EprQuantifiedEqualityAtom> unifiedDoublyQuantifiedEqualitiesA = 
				new ArrayList<EprQuantifiedEqualityAtom>();
		ArrayList<EprQuantifiedEqualityAtom> unifiedDoublyQuantifiedEqualitiesB = 
				new ArrayList<EprQuantifiedEqualityAtom>();

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
		
		////// handle ground equalities

		//note: if we did not specialize B, we can only have ground equalities on the A side, right??
		// however: the clause where B came from might have ground equalities... 
		//  ...?

		if (!unifiedGroundEqualitiesA.isEmpty()) {
			// this means in effect that the implication holds given the ground equalities do not hold
			// false is sound
			// maybe would be more complete to do sth else (ask state manager if they are different ..)
			// also: if all the ground equalities in A are also present in B (might have to look at the rest of the clause)
			//       then the implication holds..
			assert false : "think..";
			return false;
		}
		
		/////// handle non-ground equalities
		// (check subset, basically..)
		boolean singlySubset = true;
		for (Entry<TermVariable, HashSet<ApplicationTerm>> en1 : unifiedSinglyQuantifiedEqualitiesAasMap.entrySet()) {
			HashSet<ApplicationTerm> bValue = unifiedSinglyQuantifiedEqualitiesBasMap.get(en1.getKey());
			if (bValue == null) {
				singlySubset = false;
				break;
			}
			if (!bValue.containsAll(en1.getValue())) {
				singlySubset = false;
				break;
			}
		}
		if (!singlySubset)
			return false;
		
		/////// handle doubly quantified equalities

		// subset check.. 
		//TODO: verify the thinking here..
		boolean doublySubset = true;
		for (EprQuantifiedEqualityAtom eqA : unifiedDoublyQuantifiedEqualitiesA) {
			boolean isContained = false;
			for (EprQuantifiedEqualityAtom eqB : unifiedDoublyQuantifiedEqualitiesB) {
				if (eqA.getTerm().equals(eqB.getTerm()) 
						|| (eqA.getLhs() == eqB.getRhs() && eqA.getRhs() == eqB.getLhs())) {
					isContained = true;
					break;
				}
			}
			if (!isContained) {
				doublySubset = false;
				break;
			}
		}
		if (!doublySubset)
			return false;

		return true;
	}

	/**
	 * @param sub
	 * @param litA
	 * @return
	 */
	private boolean doesUnifierSpecialize(TTSubstitution sub, Literal litA) {
		TermTuple tt = ((EprPredicateAtom) litA.getAtom()).getArgumentsAsTermTuple();
		TermTuple subTt = sub.apply(tt);
		boolean result = false;
		// check if a variable becomes a constant
		for (int i = 0; i < tt.terms.length; i++) {
			if (tt.terms[i] instanceof TermVariable
					&& subTt.terms[i] instanceof ApplicationTerm)
				result = true;
			if (tt.terms[i] instanceof ApplicationTerm
					&& subTt.terms[i] instanceof ApplicationTerm
					&& tt.terms[i] != subTt.terms[i])
				assert false : "what do we do in this case?"; //(no specialisation as long as the equality holds..
		}
		// check if two different variables become one (naive implementation..)
		for (int i = 0; i < tt.terms.length; i++) {
			for (int j = i + 1; j < tt.terms.length; j++) {
				if (tt.terms[i] != tt.terms[j]
						&& tt.terms[i] instanceof TermVariable
						&& tt.terms[j] instanceof TermVariable
						&& subTt.terms[i] == subTt.terms[j])
					return false;
			}
		}
		return result;
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
						hs = new HashSet<ApplicationTerm>();
						singlyQuantifiedEqualitiesAsMap.put(tv, hs);
					}
					hs.add(at);
				}
			}
		}
	}
	
	public HashSet<ApplicationTerm> getAppearingConstants() {
		return mAppearingConstants;
	}

	enum ResolventStatus {
		Tautology, Conflict, ForcesFinite, Ground
	}

	class GetResolventStatus {
		ResolventStatus rs;
		EprClauseOld resolvent;

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
					eq1, eq2, subs, mEprTheory);										
			resolvent = 
					new EprDerivedClause(substEqualities, mEprTheory, this);

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
		
		EprClauseOld getResolvent() {
			return resolvent;
		}
	}

	public List<Literal[]> computeAllGroundings(List<TTSubstitution> allInstantiations) {
		ArrayList<Literal[]> result = new ArrayList<Literal[]>();
		for (TTSubstitution sub : allInstantiations) {
			ArrayList<Literal> groundInstList = getSubstitutedLiterals(sub);
			result.add(groundInstList.toArray(new Literal[groundInstList.size()]));
		}
		
		return result;
	}

	public List<Literal[]> computeAllGroundings(HashSet<ApplicationTerm> constants) {
		
		List<TTSubstitution> allInstantiations =  
				mStateManager.getAllInstantiations(this.getFreeVars(), constants);
		
		return computeAllGroundings(allInstantiations);
	}
}
