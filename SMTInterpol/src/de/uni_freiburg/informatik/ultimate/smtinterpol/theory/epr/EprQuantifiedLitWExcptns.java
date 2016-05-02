package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
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
public class EprQuantifiedLitWExcptns extends EprUnitClause {
	
	public EprQuantifiedLitWExcptns(Literal[] literals, Theory theory, EprStateManager stateManager,
			Object explanation) {
		super(literals, theory, stateManager, explanation);
		assert eprQuantifiedPredicateLiterals.length == 1;
		assert groundLiterals.length == 0;
		mPredicateLiteral = eprQuantifiedPredicateLiterals[0];
	}

	Literal mPredicateLiteral;

	// quantified atom
	private EprQuantifiedPredicateAtom mAtom;

	// exceptions
	EprEqualityAtom[] mExceptions;

	// explanation
	EprClause mExplanation;

	public String toString() {
		String not = mPredicateLiteral.getSign() == 1 ? "" : "! ";
//		return  not + mAtom.toString() + "\\" + mExceptedPoints.toString();
		return  not + mAtom.toString() + "\\" + mExceptions.toString();
	}

	public Literal getPredicateLiteral() {
		return mPredicateLiteral;
	}

	public EprQuantifiedPredicateAtom getPredicateAtom() {
		return mAtom;
	}
	
	
	/**
	 * Computes the clause obtained by applying resolution to this and eqlwe
	 * @param eql another EprQuantifiedLitWExcptns, which has the same predicate and different polarity
	 * @return if there is a unifier: a set of literals representing the resolvent clause.
	 *         otherwise: null.
	 */
	public EprClause resolveAgainst(EprQuantifiedLitWExcptns eqlwe, 
			TTSubstitution sub, Theory theory, int stackLevel) {
		assert eqlwe.getPredicateLiteral().getSign() != this.getPredicateLiteral().getSign();
		assert eqlwe.mAtom.eprPredicate == this.mAtom.eprPredicate;

		ArrayList<Literal> result = new ArrayList<>();
		for (EprEqualityAtom eea : mExceptions) {
			result.add(EprHelpers.applySubstitution(sub, eea, theory));
		}
		for (EprEqualityAtom eea : eqlwe.mExceptions) {
			result.add(EprHelpers.applySubstitution(sub, eea, theory));
		}
		return new EprClause(result.toArray(new Literal[result.size()]), stackLevel, theory);
	}

	/**
	 * Computes the clause obtained by applying resolution to this and eqpa
	 * @param eql a predicate atom which is assumed to have different polarity from this.mIsPositive
	 * @return if there is a unifier: a set of literals representing the resolvent clause.
	 *         otherwise: null.
	 */
	public EprClause resolveAgainst(EprPredicateAtom eqpa, 
			TTSubstitution sub, Theory theory, int stackLevel) {
		assert eqpa.eprPredicate == this.mAtom.eprPredicate;
		
//		TTSubstitution sub = this.mAtom.getArgumentsAsTermTuple().
//				match(eqpa.getArgumentsAsTermTuple(), eqman);
//		
//		if (sub == null)
//			return null;
		
		ArrayList<Literal> result = new ArrayList<>();
		for (EprEqualityAtom eea : mExceptions) {
			result.add(EprHelpers.applySubstitution(sub, eea, theory));
		}
		return new EprClause(result.toArray(new Literal[result.size()]), stackLevel, theory);
	}
	

	public ArrayList<DPLLAtom> substituteInExceptions(
			TTSubstitution sub, Theory theory) {
		//TODO: remove the resolveAgainst-uses in favour of this method
		
		ArrayList<DPLLAtom> result = new ArrayList<>();
		for (EprEqualityAtom eea : mExceptions) {
			result.add((DPLLAtom) EprHelpers.applySubstitution(sub, eea, theory));
		}
		return result;
	}
}
