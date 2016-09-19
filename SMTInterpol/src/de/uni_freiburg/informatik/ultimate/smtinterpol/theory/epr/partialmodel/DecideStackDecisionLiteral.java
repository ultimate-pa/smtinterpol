package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

/**
 * Represents a literal on the decide stack that was set because of a decision of the epr
 * solver (rather than a propagation..).
 * 
 * @author nutz
 */
public class DecideStackDecisionLiteral extends DecideStackLiteral {

	public DecideStackDecisionLiteral(boolean polarity, EprPredicate eprPredicate, 
			IDawg<ApplicationTerm, TermVariable> dawg, Pair<Integer, Integer> index) {
		super(polarity, eprPredicate, dawg, index);
	}

	@Override
	public String toString() {
		return String.format("(DSDec (%d,%d): %c%b)", 
				mIndex.indexOfPushState, mIndex.indexOnPushStatesDecideStack, mPolarity ? ' ' : '~',  mPred);
	}	
}
