package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprStateManager;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;

/**
 * Stands for a clause of that contains one quantified literal built from an uninterpreted predicate,
 * and an arbitrary number of quantified equalities.
 * The predicate literal may be positive or negative, the equalities must be positive.
 *  example: (or (not (P x y z a)) (= x a) (= x b) (= y z) ...)
 *  
 * @author nutz
 */
public class EprQuantifiedUnitClause extends EprUnitClause {
	
	public EprQuantifiedUnitClause(Literal[] literals, EprTheory eprTheory,
			EprClause explanation) {
		this(literals, eprTheory, explanation, false, null);
	}
	
	public EprQuantifiedUnitClause(Literal[] literals, EprTheory eprTheory,
			EprClause explanation, boolean freshAlphaRenaming, TTSubstitution freshAlphaRen) {
		super(literals, eprTheory, explanation, freshAlphaRenaming, freshAlphaRen);
		assert eprQuantifiedPredicateLiterals.length == 1;
		assert groundLiterals.length == 0;
		mPredicateLiteral = eprQuantifiedPredicateLiterals[0];
		mExceptions = eprQuantifiedEqualityAtoms;
		mAtom = (EprQuantifiedPredicateAtom) mPredicateLiteral.getAtom();
	}

	Literal mPredicateLiteral;

	// quantified atom
	private EprQuantifiedPredicateAtom mAtom;

	// exceptions
	EprQuantifiedEqualityAtom[] mExceptions;

	public String toString() {
		return  mPredicateLiteral.toString() + "\\" + Arrays.toString(mExceptions);
	}

	public Literal getPredicateLiteral() {
		return mPredicateLiteral;
	}

	public EprQuantifiedPredicateAtom getPredicateAtom() {
		return mAtom;
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

	@Override
	public EprQuantifiedUnitClause getFreshAlphaRenamedVersion() {
		TTSubstitution sub = new TTSubstitution();
		ArrayList<Literal> newLits = getFreshAlphaRenamedLiterals(sub);
		return new EprQuantifiedUnitClause(newLits.toArray(new Literal[newLits.size()]), 
				mEprTheory, mExplanation, true, sub);
	}
}
