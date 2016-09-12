package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

public class EprGroundPredicateLiteral implements IEprLiteral {
	
	private final EprGroundPredicateAtom mAtom;
	private final EprPredicate mEprPredicate;
	private final boolean mPolarity;
	private final IDawg<ApplicationTerm, TermVariable> mDawg;
	
	public EprGroundPredicateLiteral(Literal l, DawgFactory<ApplicationTerm, TermVariable> dawgFactory) {
		mAtom = (EprGroundPredicateAtom) l.getAtom();
		mEprPredicate = mAtom.mEprPredicate;
		mPolarity = l.getSign() == 1;
		mDawg = 
				dawgFactory.createOnePointDawg(
						mEprPredicate.getTermVariablesForArguments(), 
						EprHelpers.convertTermArrayToConstantList(mAtom.getArguments()));
	}

	@Override
	public EprPredicate getEprPredicate() {
		return mEprPredicate;
	}

	@Override
	public boolean getPolarity() {
		return mPolarity;
	}

	@Override
	public IDawg<ApplicationTerm, TermVariable> getDawg() {
		return mDawg;
	}

	@Override
	public String toString() {
		return "(EGPL: " + (mPolarity ? mAtom : mAtom.negate()).toString() + ")";
	}
}
