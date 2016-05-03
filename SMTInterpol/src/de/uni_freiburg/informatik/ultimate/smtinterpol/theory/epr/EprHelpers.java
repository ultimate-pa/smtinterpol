package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

public class EprHelpers {

	/**
	 * Apply the substitution sub to Literal l, return the result
	 * @param sub
	 * @param l
	 * @param theory
	 * @return
	 */
//	public static Literal applySubstitution(TTSubstitution sub, Literal l, Theory theory, CClosure cClosure) {
	public static Literal applySubstitution(TTSubstitution sub, Literal l, Theory theory) {
		boolean isPositive = l.getSign() == 1;
		DPLLAtom atom = l.getAtom();

		if (atom instanceof EprQuantifiedPredicateAtom) {
			EprQuantifiedPredicateAtom eqpa = (EprQuantifiedPredicateAtom) atom;
			TermTuple newTT = sub.apply(eqpa.getArgumentsAsTermTuple());
			ApplicationTerm newTerm = theory.term(eqpa.eprPredicate.functionSymbol, newTT.terms);
			EprPredicateAtom result = null;
			if (newTerm.getFreeVars().length > 0) {
				result = eqpa.eprPredicate.getAtomForTermTuple(newTT, theory, l.getAtom().getAssertionStackLevel());
			} else {
				result = eqpa.eprPredicate.getAtomForPoint(newTT, theory, l.getAtom().getAssertionStackLevel());
			}
			return isPositive ? result : result.negate();
		} else if (atom instanceof EprEqualityAtom) {
			EprEqualityAtom eea = (EprEqualityAtom) atom;
			TermTuple newTT = sub.apply(eea.getArgumentsAsTermTuple());
			ApplicationTerm newTerm = theory.term("=", newTT.terms);
			DPLLAtom result = null;
			if (newTerm.getFreeVars().length > 0) {
				result = new EprEqualityAtom(newTerm, 0, l.getAtom().getAssertionStackLevel());//TODO: hash
//			} else if (newTerm.getParameters()[0].equals(newTerm.getParameters()[1])) {
			} else {
//				TODO: will need a management for these atoms -- so there are no duplicates..
				return new EprGroundEqualityAtom(newTerm, 0, 0);
			}
			return isPositive ? result : result.negate();
		} else {
			assert false : "there might be equality replacements";
			return l;
		}
	}

	public static EprQuantifiedUnitClause buildEQLWE(
//			boolean isPositive, 
//			EprQuantifiedPredicateAtom atom, 
			Literal quantifiedPredicateLiteral,
			EprEqualityAtom[] excep,
			EprClause explanation,
			Theory theory,
			EprStateManager stateManager) {
		assert quantifiedPredicateLiteral.getAtom() instanceof EprQuantifiedPredicateAtom;

		Literal[] lits = new Literal[excep.length + 1];
		for (int i = 0; i < excep.length; i++) {
			lits[i] = excep[i];
		}
//		lits[lits.length - 1] = isPositive ? atom : atom.negate();
		lits[lits.length - 1] = quantifiedPredicateLiteral;

		return new EprQuantifiedUnitClause(lits, theory, stateManager, explanation);
	}
	
	/**
	 * sub is a unifier for the predicateAtoms in setEqlwe and clauseLit.
	 * Apply sub to the equalities in setEqlwe and eprEqualityAtoms,
	 * return the result as a clause.
	 * @param setEqlwe
	 * @param clauseLit
	 * @param eprEqualityAtoms
	 * @param sub
	 * @return
	 */
	public static Literal[] applyUnifierToEqualities(EprEqualityAtom[] eprEqualityAtoms1,
			EprEqualityAtom[] eprEqualityAtoms2, TTSubstitution sub, Theory theory) {
		
		ArrayList<Literal> result = new ArrayList<>();
		for (EprEqualityAtom eea : eprEqualityAtoms1) 
			result.add(EprHelpers.applySubstitution(sub, eea, theory));
		for (EprEqualityAtom eea : eprEqualityAtoms2)
			result.add(EprHelpers.applySubstitution(sub, eea, theory));

		return result.toArray(new Literal[result.size()]);
	}
}
