package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

/**
 * Represents a literal on the DPLL decide stack of the EprTheory.
 * This special literal consists of a quantified literal together with a 
 * data structure restricting the possible groundings of that literal.
 * 
 * @author nutz
 */
public abstract class DecideStackLiteral {

	boolean mPolarity;
	EprPredicateAtom mAtom;
	EprPredicate mPred;

	public DecideStackLiteral(boolean polarity, EprPredicateAtom atom) {
		mPolarity = polarity;
		mAtom = atom;
		mPred = mAtom.getEprPredicate();
	}

	public DecideStackLiteral(boolean polarity, EprPredicate pred) {
		mPolarity = polarity;
		mPred = pred;
	}

	public boolean getPolarity() {
		return mPolarity;
	}
	
	public EprPredicateAtom getAtom() {
		return mAtom;
	}
	
	public EprPredicate getEprPredicate() {
		return mPred;
	}

	/**
	 * Checks if this literal's dawg talks about the point described by arguments.
	 * arguments may only contain constants.
	 * @param arguments
	 * @return
	 */
	public boolean talksAboutPoint(Term[] arguments) {
		assert false : "TODO: implement";
		return false;
	}

	public IDawg<ApplicationTerm, TermVariable> getDawg() {
		assert false : "TODO: implement";
		return null;
	}
}
