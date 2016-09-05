package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgTranslation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;

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
	private Map<TermVariable, Object> mTranslationForClause;

	public ClauseEprQuantifiedLiteral(boolean polarity, EprQuantifiedPredicateAtom atom, 
			EprClause clause, EprTheory eprTheory) {
		super(polarity, atom, clause, eprTheory);
		mAtom = atom;

		processAtom(atom);			
		
		mTranslationForClause = getTranslationForClause();
	}

	/**
	 * Collect all the information from the EprQuantifiedPredicateAtom and store it in a way
	 * we can use it easily later.
	 * @param atom
	 */
	private void processAtom(EprQuantifiedPredicateAtom atom) {
//		mArgumentTerms = 
//				new ArrayList<Term>();
		TreeSet<TermVariable> clSig = new TreeSet<TermVariable>(EprHelpers.getColumnNamesComparator());

		for (int i = 0; i < atom.getArguments().length; i++) {
			Term argI = atom.getArguments()[i];

//			TermVariable tv = null;
//			if (argI instanceof TermVariable) {
//				tv = (TermVariable) argI;
//			} else if (argI instanceof ApplicationTerm) {
//				ApplicationTerm at = (ApplicationTerm) argI;
//				assert at.getParameters().length == 0;
//				tv = mEprTheory.getTheory().createFreshTermVariable(argI.toString(), argI.getSort());
//				mVariableToConstant.put(tv, at);
//			} else {
//				assert false;
//			}
//			mArgumentTerms.add(tv);

//			mArgumentTerms.add(argI);

//			mEprClause.updateVariableToClauseLitToPosition(tv, this, i);
			if (argI instanceof TermVariable) {
				mEprClause.updateVariableToClauseLitToPosition((TermVariable) argI, this, i);
				clSig.add((TermVariable) argI);
			}
		}
		
		mDawgSignature = Collections.unmodifiableSortedSet(clSig);
	}

	public void addExceptions(Set<EprQuantifiedEqualityAtom> quantifiedEqualities) {
		assert false : "TODO: implement";
	}

	/**
	 * Fill the map identicalVariablePositionsInOtherClauseLiterals
	 * (needs to be triggered after all literals have been added to the clause)
	 */
	public void updateIdenticalVariablePositions() {
		for (int i = 0; i < mAtom.getArguments().length; i++) {
			if (! (mAtom.getArguments()[i] instanceof TermVariable))
				continue;
			TermVariable tv = (TermVariable) mAtom.getArguments()[i];
			Map<ClauseEprQuantifiedLiteral, Set<Integer>> clToPos = mEprClause.getClauseLitToPositions(tv);

			for (Entry<ClauseEprQuantifiedLiteral, Set<Integer>> en : clToPos.entrySet()) {
				Map<ClauseEprQuantifiedLiteral, Set<Integer>> otherClToIdenticalPos = 
						identicalVariablePositionsInOtherClauseLiterals.get(i);
				
				if (otherClToIdenticalPos == null) {
					otherClToIdenticalPos = new HashMap<ClauseEprQuantifiedLiteral, Set<Integer>>();
					identicalVariablePositionsInOtherClauseLiterals.put(i, otherClToIdenticalPos);
				}
				otherClToIdenticalPos.put(en.getKey(), en.getValue());
			}
		}
	}

	/**
	 * Returns the points where this literal is fulfillable in the decide state that was current when
	 * isFulfillable was last called.
	 * To prevent some misusage, this nulls the field so it is not used twice.
	 *  --> however this will still be problematic if the state changes between the last call to isFulfillable
	 *  and this method.
	 * @return
	 */
	public IDawg<ApplicationTerm, TermVariable> getFulfillablePoints() {
		assert mFulfillablePoints != null;
		IDawg<ApplicationTerm, TermVariable> result = mFulfillablePoints;
		mFulfillablePoints = null;
		return result;
	}

	public IDawg<ApplicationTerm, TermVariable> getFulfilledPoints() {
		assert mFulfilledPoints != null;
		IDawg<ApplicationTerm, TermVariable> result = mFulfilledPoints;
		mFulfilledPoints = null;
		return result;
	}

	public IDawg<ApplicationTerm, TermVariable> getRefutedPoints() {
		assert mRefutedPoints != null;
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
		for (DecideStackLiteral dsl : mPartiallyConflictingDecideStackLiterals) {
			refutedPoints.addAll(dsl.getDawg());
		}
		// right now, the refuted points are in terms of the EprPredicates signature, we need a renaming
		// and possibly select and projects to match the signature of the ClauseLiteral relative to the clause.
		refutedPoints = mDawgFactory.renameSelectAndProject(refutedPoints, mTranslationForClause);

//		// rename the dawgs columns so they match the clauseLiteral
//		refutedPoints = mEprTheory.getDawgFactory().renameColumnsOfDawg(refutedPoints, mTranslationForClause);
//		// select only lines that match the constants
//		refutedPoints = mEprTheory.getDawgFactory().select(refutedPoints, mVariableToConstant);


		// collect the points in a dawg with the predicate's signature
		IDawg<ApplicationTerm, TermVariable> fulfilledPoints = 
				mEprTheory.getDawgFactory().createEmptyDawg(mAtom.getEprPredicate().getTermVariablesForArguments());
		for (DecideStackLiteral dsl : mPartiallyFulfillingDecideStackLiterals) {
			fulfilledPoints.addAll(dsl.getDawg());
		}
		// right now, the refuted points are in terms of the EprPredicates signature, we need a renaming
		// and possibly select and projects to match the signature of the ClauseLiteral relative to the clause.
		refutedPoints = mDawgFactory.renameSelectAndProject(refutedPoints, mTranslationForClause);

//		// rename the dawgs columns so they match the clauseLiteral
//		fulfilledPoints = mEprTheory.getDawgFactory().renameColumnsOfDawg(fulfilledPoints, mTranslationForClause);
//		// select only lines that match the constants
//		fulfilledPoints = mEprTheory.getDawgFactory().select(fulfilledPoints, mVariableToConstant);

		mFulfillablePoints = mEprTheory.getDawgFactory().createFullDawg(mDawgSignature);

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
//	public DawgTranslation<TermVariable> getTranslationForClause() {
	private Map<TermVariable, Object> getTranslationForClause() {

//		DawgTranslation<TermVariable> dt = new DawgTranslation<TermVariable>();
//		for ()
		Map<TermVariable, Object> result = 
				new HashMap<TermVariable, Object>();
		Iterator<TermVariable> predTermVarIt = mAtom.getEprPredicate().getTermVariablesForArguments().iterator();
		for (int i = 0; i < mArgumentTerms.size(); i++) {
			Term atomT = mArgumentTerms.get(i);
			result.put(
					predTermVarIt.next(),
					atomT);
		}
		return result;
	}
	

}
