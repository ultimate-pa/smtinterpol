package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;

/**
 * Represents a literal on the DPLL decide stack of the EprTheory.
 * This special literal consists of a quantified literal together with a 
 * data structure restricting the possible groundings of that literal.
 * 
 * @author nutz
 */
public class DecideStackLiteral {

	boolean mPolarity;
	EprPredicateAtom mAtom;

	public DecideStackLiteral(boolean polarity, EprPredicateAtom atom) {
		mPolarity = polarity;
		mAtom = atom;
	}

}
