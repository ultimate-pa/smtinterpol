package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprQuantifiedPredicateAtom;

/**
 * Stands for a clause of that contains one quantified literal built from an uninterpreted predicate,
 * and an arbitrary number of quantified equalities.
 * The predicate literal may be positive or negative, the equalities must be positive.
 *  example: (or (not (P x y z a)) (= x a) (= x b) (= y z) ...)
 *  
 * @author nutz
 */
public class EprQuantifiedUnitClause extends EprUnitClause {
	
	public EprQuantifiedUnitClause(Literal[] literals, Theory theory, EprStateManager stateManager,
			EprClause explanation) {
		super(literals, theory, stateManager, explanation);
		assert eprQuantifiedPredicateLiterals.length == 1;
		assert groundLiterals.length == 0;
		mPredicateLiteral = eprQuantifiedPredicateLiterals[0];
		mExceptions = eprEqualityAtoms;
		mAtom = (EprQuantifiedPredicateAtom) mPredicateLiteral.getAtom();
	}

	Literal mPredicateLiteral;

	// quantified atom
	private EprQuantifiedPredicateAtom mAtom;

	// exceptions
	EprEqualityAtom[] mExceptions;

	public String toString() {
		return  mPredicateLiteral.toString() + "\\" + Arrays.toString(mExceptions);
	}

	public Literal getPredicateLiteral() {
		return mPredicateLiteral;
	}

	public EprQuantifiedPredicateAtom getPredicateAtom() {
		return mAtom;
	}
	
	/**
	 * Computes the clause obtained by applying resolution to this and eqlwe
	 * 
	 * Note:
	 * also allowing the case where the polarities of the two quantified predicate literals
	 * don't differ
	 *   --> in that case the result is not really 
	 * @param eql another EprQuantifiedLitWExcptns, which has the same predicate and different polarity
	 * @return if there is a unifier: a set of literals representing the resolvent clause.
	 *         otherwise: null.
	 */
	public EprClause resolveAgainst(EprQuantifiedUnitClause eqlwe, 
			TTSubstitution sub) {
//		assert eqlwe.getPredicateLiteral().getSign() != this.getPredicateLiteral().getSign();
		assert eqlwe.mAtom.eprPredicate == this.mAtom.eprPredicate;

		ArrayList<Literal> result = new ArrayList<>();
		for (EprEqualityAtom eea : mExceptions) {
//			result.add(EprHelpers.applySubstitution(sub, eea, mTheory, mStateManager.getCClosure()));
			result.add(EprHelpers.applySubstitution(sub, eea, mTheory));
		}
		for (EprEqualityAtom eea : eqlwe.mExceptions) {
//			result.add(EprHelpers.applySubstitution(sub, eea, mTheory, mStateManager.getCClosure()));
			result.add(EprHelpers.applySubstitution(sub, eea, mTheory));
		}
		return new EprDerivedClause(result.toArray(new Literal[result.size()]), mTheory, mStateManager, this);
	}

	/**
	 * Computes the clause obtained by applying resolution to this and eqpa
	 * @param eql a predicate atom which is assumed to have different polarity from this.mIsPositive
	 * @return if there is a unifier: a set of literals representing the resolvent clause.
	 *         otherwise: null.
	 */
	public EprClause resolveAgainst(EprPredicateAtom eqpa, 
			TTSubstitution sub) {
		assert eqpa.eprPredicate == this.mAtom.eprPredicate;
		
//		TTSubstitution sub = this.mAtom.getArgumentsAsTermTuple().
//				match(eqpa.getArgumentsAsTermTuple(), eqman);
//		
//		if (sub == null)
//			return null;
		
		ArrayList<Literal> result = new ArrayList<>();
		for (EprEqualityAtom eea : mExceptions) {
//			result.add(EprHelpers.applySubstitution(sub, eea, mTheory, mStateManager.getCClosure()));
			result.add(EprHelpers.applySubstitution(sub, eea, mTheory));
		}
		return new EprDerivedClause(result.toArray(new Literal[result.size()]), mTheory, mStateManager, this);
	}
	

	public ArrayList<DPLLAtom> substituteInExceptions(
			TTSubstitution sub, Theory theory) {
		//TODO: remove the resolveAgainst-uses in favor of this method
		
		ArrayList<DPLLAtom> result = new ArrayList<>();
		for (EprEqualityAtom eea : mExceptions) {
//			result.add((DPLLAtom) EprHelpers.applySubstitution(sub, eea, theory, mStateManager.getCClosure()));
			result.add((DPLLAtom) EprHelpers.applySubstitution(sub, eea, theory));
		}
		return result;
	}

	@Override
	public boolean isConflictClause() {
		assert false : "TODO";
		return false;
	}

	@Override
	public EprUnitClause getUnitClauseLiteral() {
		assert false : "TODO";
		return null;
	}
}
