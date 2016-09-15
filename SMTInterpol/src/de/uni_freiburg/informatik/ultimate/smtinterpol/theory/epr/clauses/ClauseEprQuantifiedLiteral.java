package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution.SubsPair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.IEprLiteral;

public class ClauseEprQuantifiedLiteral extends ClauseEprLiteral {

	EprQuantifiedPredicateAtom mAtom;
	
	
	/**
	 * Used for storing when a quantified literal has a constant in one or more arguments:
	 *  For P(a, x, b), we will store a ClauseLiteral P(tv_a, x, tv_b) where tv_a and tv_b
	 *  are fresh TermVariables, while in this map we will store that tv_a is instantiated with
	 *  a and tv_b analogously.
	 *  tv_a and tv_b do _not_ occur in 
	 */
	private Map<TermVariable, ApplicationTerm> mVariableToConstant;

	
	/**
	 * stores variable identities between different quantified literals in the same clause
	 * (for example would remember that in the clause {P(x, y), Q(y, z)} the second position of
	 *  the P-literal and the first position of the Q-literal have the same variable)
	 *  
	 *  Once we have filled this map, we can forget the concrete TermVariables.
	 */
	Map<Integer, Map<ClauseEprQuantifiedLiteral, Set<Integer>>> identicalVariablePositionsInOtherClauseLiterals = 
			new HashMap<Integer, Map<ClauseEprQuantifiedLiteral,Set<Integer>>>();
	
	/**
	 * Stores the points where this literal is currently fulfillable.
	 *  -- this is only updated on an isFulfillable query, so it should
	 *  only be non-null between a call to isFulfillable() and getFulfillablePoints()
	 */
	IDawg<ApplicationTerm, TermVariable> mFulfillablePoints;

	IDawg<ApplicationTerm, TermVariable> mFulfilledPoints;

	IDawg<ApplicationTerm, TermVariable> mRefutedPoints;

	/**
	 * The Dawg signature for the representation of points wrt this Clause literal.
	 * Note that this signature may be shorter than the list mArgumentTermVariables if
	 *  that list contains repetitions and/or constants
	 */
	private SortedSet<TermVariable> mDawgSignature;

	/**
	 * Translates the EprPredicates signature to the signature that this ClauseLit has.
	 * I.e. translates mAtom.getEprPredicate().getArguments() to mArgumentTermVariables.
	 * In effect, we use this translation for the unification/natural join with the
	 * decide stack literals, which have a canonical signature from their EprPredicate. 
	 */
	private final Map<TermVariable, Object> mTranslationForClause;
	
	
	/**
	 * Roughly the reverse of mTranslationForClause.
	 * Translates from the variable names of the EprClause this ClauseLiteral belongs to into
	 * the canoncal variable names of the EprPredicate.
	 * Used for translating from unit clause representation as a dawg over the clause signature
	 * to a dawg over the predicate's signature.
	 */
	private final Map<TermVariable, TermVariable> mTranslationForEprPredicate;

	public ClauseEprQuantifiedLiteral(boolean polarity, EprQuantifiedPredicateAtom atom, 
			EprClause clause, EprTheory eprTheory) {
		super(polarity, atom, clause, eprTheory);
		mAtom = atom;

		// compute the signature of a dawg that describes points where this literal has some state
		SortedSet<TermVariable> vars = new TreeSet<TermVariable>(EprHelpers.getColumnNamesComparator());
		for (Term arg : atom.getArguments()) {
			if (arg instanceof TermVariable) {
				vars.add((TermVariable) arg);
			}
		}
		mDawgSignature = Collections.unmodifiableSortedSet(vars);

		Pair<Map<TermVariable, Object>, Map<TermVariable, TermVariable>> p = computeDawgSignatureTranslations();
		mTranslationForClause = p.first;
		mTranslationForEprPredicate = p.second;
	}

//	/**
//	 * Collect all the information from the EprQuantifiedPredicateAtom and store it in a way
//	 * we can use it easily later.
//	 * @param atom
//	 */
//	private void processAtom(EprQuantifiedPredicateAtom atom) {
////		mArgumentTerms = 
////				new ArrayList<Term>();
//		TreeSet<TermVariable> clSig = new TreeSet<TermVariable>(EprHelpers.getColumnNamesComparator());
//
//		for (int i = 0; i < atom.getArguments().length; i++) {
//			Term argI = atom.getArguments()[i];
//
////			TermVariable tv = null;
////			if (argI instanceof TermVariable) {
////				tv = (TermVariable) argI;
////			} else if (argI instanceof ApplicationTerm) {
////				ApplicationTerm at = (ApplicationTerm) argI;
////				assert at.getParameters().length == 0;
////				tv = mEprTheory.getTheory().createFreshTermVariable(argI.toString(), argI.getSort());
////				mVariableToConstant.put(tv, at);
////			} else {
////				assert false;
////			}
////			mArgumentTerms.add(tv);
//
////			mArgumentTerms.add(argI);
//
////			mEprClause.updateVariableToClauseLitToPosition(tv, this, i);
//			if (argI instanceof TermVariable) {
////				mEprClause.updateVariableToClauseLitToPosition((TermVariable) argI, this, i);
//				clSig.add((TermVariable) argI);
//			}
//		}
//		
//		mDawgSignature = Collections.unmodifiableSortedSet(clSig);
//	}

	public void addExceptions(Set<EprQuantifiedEqualityAtom> quantifiedEqualities) {
		for (EprQuantifiedEqualityAtom eqea : quantifiedEqualities) {
			assert false : "TODO: implement";
		}
	}

//	/**
//	 * Fill the map identicalVariablePositionsInOtherClauseLiterals
//	 * (needs to be triggered after all literals have been added to the clause)
//	 */
//	public void updateIdenticalVariablePositions() {
//		for (int i = 0; i < mAtom.getArguments().length; i++) {
//			if (! (mAtom.getArguments()[i] instanceof TermVariable))
//				continue;
//			TermVariable tv = (TermVariable) mAtom.getArguments()[i];
//			Map<ClauseEprQuantifiedLiteral, Set<Integer>> clToPos = mEprClause.getClauseLitToPositions(tv);
//
//			for (Entry<ClauseEprQuantifiedLiteral, Set<Integer>> en : clToPos.entrySet()) {
//				Map<ClauseEprQuantifiedLiteral, Set<Integer>> otherClToIdenticalPos = 
//						identicalVariablePositionsInOtherClauseLiterals.get(i);
//				
//				if (otherClToIdenticalPos == null) {
//					otherClToIdenticalPos = new HashMap<ClauseEprQuantifiedLiteral, Set<Integer>>();
//					identicalVariablePositionsInOtherClauseLiterals.put(i, otherClToIdenticalPos);
//				}
//				otherClToIdenticalPos.put(en.getKey(), en.getValue());
//			}
//		}
//	}

	/**
	 * Returns the points where this literal is fulfillable in the decide state that was current when
	 * isFulfillable was last called.
	 * To prevent some misusage, this nulls the field so it is not used twice.
	 *  --> however this will still be problematic if the state changes between the last call to isFulfillable
	 *  and this method.
	 *  
	 *  Convention: fulfillablePoints (like refuted and fulfilled points) are returned in the signature of the _clause_!
	 * @return
	 */
	public IDawg<ApplicationTerm, TermVariable> getFulfillablePoints() {
		assert mFulfillablePoints != null;
		assert mFulfillablePoints.getColnames().equals(mEprClause.getVariables());
		IDawg<ApplicationTerm, TermVariable> result = mFulfillablePoints;
		mFulfillablePoints = null;
		return result;
	}

	public IDawg<ApplicationTerm, TermVariable> getFulfilledPoints() {
		assert mFulfilledPoints != null;
		assert mFulfilledPoints.getColnames().equals(mEprClause.getVariables());
		IDawg<ApplicationTerm, TermVariable> result = mFulfilledPoints;
		mFulfilledPoints = null;
		return result;
	}

	public IDawg<ApplicationTerm, TermVariable> getRefutedPoints() {
		assert mRefutedPoints != null;
		assert mRefutedPoints.getColnames().equals(mEprClause.getVariables());
		IDawg<ApplicationTerm, TermVariable> result = mRefutedPoints;
		mRefutedPoints = null;
		return result;
	}

	/**
	 * Collect the points for this literal for each of the three values (fulfilled, fulfillable, refuted).
	 * 
	 * Note:
	 *  the dawgs we are computing for those sets 
	 *  - already have the signature of the predicate in the clause
	 *  - are immediately selected upon according to the atoms constants, i.e., if we have P(a, x, b), we 
	 *    only take points that start with a and end with b
	 *  - are immediately selected upon upon to the atoms repetitions of variables, i.e., if we have
	 *    P(x, x, y), and the predicate signature is P(u, v, w) we only take points that where the entries
	 *    for u and v are equal. 
	 */
	@Override
	protected ClauseLiteralState determineState() {
		
		// collect the points in a dawg with the predicate's signature
		IDawg<ApplicationTerm, TermVariable> refutedPoints = 
				mEprTheory.getDawgFactory().createEmptyDawg(mAtom.getEprPredicate().getTermVariablesForArguments());
		for (IEprLiteral dsl : mPartiallyConflictingDecideStackLiterals) {
			refutedPoints.addAll(dsl.getDawg());
		}
		// right now, the refuted points are in terms of the EprPredicates signature, we need a renaming
		// and possibly select and projects to match the signature of the clause.
		refutedPoints = mDawgFactory.renameSelectAndProject(refutedPoints, mTranslationForClause, mEprClause.getVariables());

		// collect the points in a dawg with the predicate's signature
		IDawg<ApplicationTerm, TermVariable> fulfilledPoints = 
				mEprTheory.getDawgFactory().createEmptyDawg(
						mAtom.getEprPredicate().getTermVariablesForArguments());
		for (IEprLiteral dsl : mPartiallyFulfillingDecideStackLiterals) {
			fulfilledPoints.addAll(dsl.getDawg());
		}
		// right now, the fulfilled points are in terms of the EprPredicates signature, we need a renaming
		// and possibly select and projects to match the signature of the clause.
		fulfilledPoints = mDawgFactory.renameSelectAndProject(fulfilledPoints, mTranslationForClause, mEprClause.getVariables());

//		mFulfillablePoints = mEprTheory.getDawgFactory().createFullDawg(mDawgSignature);
		mFulfillablePoints = mEprTheory.getDawgFactory().createFullDawg(mEprClause.getVariables());

		mFulfillablePoints.removeAll(fulfilledPoints);
		mFulfillablePoints.removeAll(refutedPoints);
		mRefutedPoints = refutedPoints;
		mFulfilledPoints = fulfilledPoints;
		
		assert refutedPoints.intersect(fulfilledPoints).isEmpty();

		if (fulfilledPoints.isUniversal()) {
			return ClauseLiteralState.Fulfilled;
		} else if (refutedPoints.isUniversal()) {
			return ClauseLiteralState.Refuted;
		} else {
			return ClauseLiteralState.Fulfillable;
		}
	}

	/**
	 * Yields a translation that translates the column names of the epr predicate this clauseLiteral is talking about
	 * to the column names of the clause that this ClauseLiteral belongs to.
	 * @return map : predicateColumnNames -> clauseColumnNames
	 */
	private Pair<Map<TermVariable, Object>, Map<TermVariable, TermVariable>> computeDawgSignatureTranslations() {

		Map<TermVariable, TermVariable> clauseToPred = 
				new HashMap<TermVariable, TermVariable>();
		Map<TermVariable, Object> predToClause = 
				new HashMap<TermVariable, Object>();
		Iterator<TermVariable> predTermVarIt = mAtom.getEprPredicate().getTermVariablesForArguments().iterator();
		for (int i = 0; i < mArgumentTerms.size(); i++) {
			Term atomT = mArgumentTerms.get(i);
			TermVariable tv = predTermVarIt.next();
			predToClause.put(tv, atomT);
			if (atomT instanceof TermVariable) {
				clauseToPred.put((TermVariable) atomT, tv);
			}
		}

		/*
		 * Note:
		 * it is an important invariant for DawgFactory.renameColumnsAndRestoreConstants(..) that the map
		 * clauseToPred's range does not contain a column in the eprPredicate's signature where this 
		 * clauseLiteral has a constant.
		 */
		assert sanitizedClauseToPred(clauseToPred, mArgumentTerms);

		return new Pair<Map<TermVariable, Object>, Map<TermVariable, TermVariable>>(predToClause, clauseToPred);
	}
	
	private boolean sanitizedClauseToPred(Map<TermVariable, TermVariable> clauseToPred, List<Term> mArgumentTerms) {
		SortedSet<TermVariable> predSig = mEprPredicateAtom.getEprPredicate().getTermVariablesForArguments();
		Map<TermVariable, Integer> predCnToIndex = EprHelpers.computeColnamesToIndex(predSig);
		for (TermVariable tv : clauseToPred.values()) {
			if (mArgumentTerms.get(predCnToIndex.get(tv)) instanceof ApplicationTerm) {
				return false;
			}
		}
		return true;
	}

	public Map<TermVariable, TermVariable> getTranslationForEprPredicate() {
		return mTranslationForEprPredicate;
	}

	@Override
	public boolean isDisjointFrom(IDawg<ApplicationTerm, TermVariable> dawg) {
		 return mDawgFactory.renameSelectAndProject(dawg, mTranslationForClause, mEprClause.getVariables()).isEmpty();
	}

	/**
	 * Return a grounding of this clause that is a unit clause which allows to propagate the given literal.
	 * @param literal a ground literal such that there exists a grounding of this clause 
	 * 		that is a unit clause where the literal is the only non-refuted literal
	 * @return a grounding of this clause that is a) unit b) has literal as its only fulfilling literal
	 */
	public Clause getUnitGrounding(Literal literal) {
		DPLLAtom atom = literal.getAtom();

		IDawg<ApplicationTerm, TermVariable> groundingDawg = null;

		EprPredicateAtom epa = (EprPredicateAtom) atom;

		assert epa.getEprPredicate() == this.getEprPredicate();

		Term[] ceqlArgs = this.mArgumentTerms.toArray(new Term[this.mArgumentTerms.size()]);
		TTSubstitution unifier = epa.getArgumentsAsTermTuple().match(new TermTuple(ceqlArgs), mEprTheory.getEqualityManager());
		assert unifier != null;
		
		// build a selectMap from the unifier --> TODO: make nicer
		Map<TermVariable, ApplicationTerm> selectMap = new HashMap<TermVariable, ApplicationTerm>();
		for (SubsPair sp : unifier.getSubsPairs()) {
			selectMap.put((TermVariable) sp.bot, (ApplicationTerm) sp.top);
		}

		groundingDawg = getClause().getClauseLitToUnitPoints().get(this);
		groundingDawg = mDawgFactory.select(groundingDawg, selectMap);

		assert groundingDawg != null && ! groundingDawg.isEmpty();

		//TODO: sample one point from the dawg, so we give a one-point dawg to getGroundings() ?..
		
		Set<Clause> groundings = getClause().getGroundings(groundingDawg);
		
		return groundings.iterator().next();
	}

}
