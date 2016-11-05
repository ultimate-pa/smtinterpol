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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.BinaryRelation;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.EprGroundPredicateLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.IEprLiteral;

public class ClauseEprQuantifiedLiteral extends ClauseEprLiteral {

	EprQuantifiedPredicateAtom mAtom;
	
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
	 * 
	 * EDIT:
	 * reversing it, seems more useful
	 *  maps from dsl signature colname to clause signature colname
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
		assert p.first != null;
		assert p.second != null;
		mTranslationForClause = p.first;
		mTranslationForEprPredicate = p.second;
	}

	public void addExceptions(Set<EprQuantifiedEqualityAtom> quantifiedEqualities) {
		for (EprQuantifiedEqualityAtom eqea : quantifiedEqualities) {
			assert false : "TODO: implement";
		}
	}

	/**
	 * Returns the points where this literal is fulfillable in the decide state that was current when
	 * isFulfillable was last called.
	 * To prevent some misusage, this nulls the field so it is not used twice.
	 *  --> however this will still be problematic if the state changes between the last call to isFulfillable
	 *  and this method.
	 *  
	 *  Convention: fulfillablePoints (like refuted and fulfilled points) are returned in the signature of the _clause_!
	 * @param decideStackBorder 
	 * @return
	 */
	public IDawg<ApplicationTerm, TermVariable> getFulfillablePoints(DecideStackLiteral decideStackBorder) {
		assert !mIsStateDirty;
		assert mFulfillablePoints.getColnames().equals(mEprClause.getVariables()) :
			"fulfillable points must be given in clause signature";
		IDawg<ApplicationTerm, TermVariable> result = mFulfillablePoints;
		return result;
	}

	public IDawg<ApplicationTerm, TermVariable> getFulfilledPoints() {
		assert !mIsStateDirty;
		assert mFulfilledPoints.getColnames().equals(mEprClause.getVariables()) :
			"fulfilled points must be given in clause signature";
		IDawg<ApplicationTerm, TermVariable> result = mFulfilledPoints;
		return result;
	}

	public IDawg<ApplicationTerm, TermVariable> getRefutedPoints() {
		assert !mIsStateDirty;
		assert mRefutedPoints.getColnames().equals(mEprClause.getVariables()) : 
			"refuted points must be given in clause signature";
		IDawg<ApplicationTerm, TermVariable> result = mRefutedPoints;
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
	 *    
	 *  @param decideStackBorder when determining the state we only look at decide stack literals below the given one
	 *                   (we look at all when decideStackBorder is null)
	 */
	@Override
	protected ClauseLiteralState determineState(DecideStackLiteral decideStackBorder) {
		mIsStateDirty = false;

		// collect the points in a dawg with the predicate's signature
		IDawg<ApplicationTerm, TermVariable> refutedPoints = 
				mEprTheory.getDawgFactory().createEmptyDawg(mAtom.getEprPredicate().getTermVariablesForArguments());
		for (IEprLiteral dsl : mPartiallyConflictingDecideStackLiterals) {
			if (decideStackBorder == null 
					|| dsl instanceof EprGroundPredicateLiteral 
					|| ((DecideStackLiteral) dsl).compareTo(decideStackBorder) < 0) {
//				refutedPoints.addAll(dsl.getDawg());
				refutedPoints = refutedPoints.union(dsl.getDawg());
			}
		}
		// right now, the refuted points are in terms of the EprPredicates signature, we need a renaming
		// and possibly select and projects to match the signature of the clause.
		refutedPoints = mDawgFactory.translatePredSigToClauseSig(refutedPoints, mTranslationForClause, mEprClause.getVariables());

		// collect the points in a dawg with the predicate's signature
		IDawg<ApplicationTerm, TermVariable> fulfilledPoints = 
				mEprTheory.getDawgFactory().createEmptyDawg(
						mAtom.getEprPredicate().getTermVariablesForArguments());
		for (IEprLiteral dsl : mPartiallyFulfillingDecideStackLiterals) {
			if (decideStackBorder == null 
					|| dsl instanceof EprGroundPredicateLiteral 
					|| ((DecideStackLiteral) dsl).compareTo(decideStackBorder) < 0) {
//				fulfilledPoints.addAll(dsl.getDawg());
				fulfilledPoints = fulfilledPoints.union(dsl.getDawg());
			}
		}
		// right now, the fulfilled points are in terms of the EprPredicates signature, we need a renaming
		// and possibly select and projects to match the signature of the clause.
		fulfilledPoints = mDawgFactory.translatePredSigToClauseSig(fulfilledPoints, mTranslationForClause, mEprClause.getVariables());

		mFulfillablePoints = mEprTheory.getDawgFactory().createFullDawg(mEprClause.getVariables());
		assert EprHelpers.verifySortsOfPoints(mFulfillablePoints, mEprClause.getVariables());

//		mFulfillablePoints.removeAll(fulfilledPoints);
		mFulfillablePoints = mFulfillablePoints.difference(fulfilledPoints);
//		mFulfillablePoints.removeAll(refutedPoints);
		mFulfillablePoints = mFulfillablePoints.difference(refutedPoints);
		mRefutedPoints = refutedPoints;
		mFulfilledPoints = fulfilledPoints;
		
		assert refutedPoints.intersect(fulfilledPoints).isEmpty();
		assert EprHelpers.verifySortsOfPoints(fulfilledPoints, mEprClause.getVariables());
		assert EprHelpers.verifySortsOfPoints(refutedPoints, mEprClause.getVariables());
		assert EprHelpers.verifySortsOfPoints(mFulfillablePoints, mEprClause.getVariables());

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
				clauseToPred.put(tv, (TermVariable) atomT);
			}
		}

		return new Pair<Map<TermVariable, Object>, Map<TermVariable, TermVariable>>(predToClause, clauseToPred);
	}

	public Map<TermVariable, TermVariable> getTranslationFromClauseToEprPredicate() {
		return mTranslationForEprPredicate;
	}
	
	public Map<TermVariable, Object> getTranslationFromEprPredicateToClause() {
		return mTranslationForClause;
	}



	@Override
	public boolean isDisjointFrom(IDawg<ApplicationTerm, TermVariable> dawg) {
		 return mDawgFactory.translatePredSigToClauseSig(dawg, mTranslationForClause, mEprClause.getVariables()).isEmpty();
	}

	@Override
	public Clause getGroundingForGroundLiteral(IDawg<ApplicationTerm, TermVariable> dawg, Literal groundLiteral) {
		ApplicationTerm term = (ApplicationTerm) groundLiteral.getAtom().getSMTFormula(mEprTheory.getTheory());
		List<ApplicationTerm> args = EprHelpers.convertTermArrayToConstantList(term.getParameters());
		
		Map<TermVariable, ApplicationTerm> selectMap = new HashMap<TermVariable, ApplicationTerm>();
		for (int i = 0; i < this.getArguments().size(); i ++) {
			if (this.getArguments().get(i) instanceof TermVariable) {
				selectMap.put((TermVariable) this.getArguments().get(i), args.get(i));
			} else {
				assert this.getArguments().get(i) == args.get(i);
			}
		}
		IDawg<ApplicationTerm, TermVariable> selDawg = dawg.select(selectMap);
		Set<Clause> groundings = getClause().getGroundings(selDawg);
		return groundings.iterator().next();
	}
}
