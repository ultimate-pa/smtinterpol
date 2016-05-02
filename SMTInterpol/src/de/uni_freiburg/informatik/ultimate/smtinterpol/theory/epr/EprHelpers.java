package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom.TrueAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

public class EprHelpers {

	/**
	 * Apply the substitution sub to Literal l, return the result
	 * @param sub
	 * @param l
	 * @param theory
	 * @return
	 */
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
			if (newTerm.getFreeVars().length == 2) {
				result = new EprEqualityAtom(newTerm, 0, l.getAtom().getAssertionStackLevel());//TODO: hash
			} else if (newTerm.getFreeVars().length == 1) {
				// we have sth like a=a --> replace with TrueAtom
				result = new TrueAtom();
			} else {
				//				result = new CCEqu
				throw new UnsupportedOperationException();
			}
			return isPositive ? result : result.negate();
		} else {
			assert false : "there might be equality replacements";
			return l;
		}
	}

	public static EprQuantifiedLitWExcptns buildEQLWE(
			boolean isPositive, 
			EprQuantifiedPredicateAtom atom, 
			EprEqualityAtom[] excep,
			EprClause explanation,
			Theory theory,
			EprStateManager stateManager) {
		Literal[] lits = new Literal[excep.length + 1];
		for (int i = 0; i < excep.length; i++) {
			lits[i] = excep[i];
		}
		lits[lits.length - 1] = isPositive ? atom : atom.negate();

		return new EprQuantifiedLitWExcptns(lits, theory, stateManager, explanation);
	}
}
