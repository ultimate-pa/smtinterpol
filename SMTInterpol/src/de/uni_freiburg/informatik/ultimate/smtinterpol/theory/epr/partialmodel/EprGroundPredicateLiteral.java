package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

public class EprGroundPredicateLiteral implements IEprLiteral {
	
	private final EprGroundPredicateAtom mAtom;
	private final EprPredicate mEprPredicate;
	private final boolean mPolarity;
	private final IDawg<ApplicationTerm, TermVariable> mDawg;

	Set<ClauseEprLiteral> mConcernedClauseLiterals = new HashSet<ClauseEprLiteral>();
	
	public EprGroundPredicateLiteral(Literal l, DawgFactory<ApplicationTerm, TermVariable> dawgFactory, EprStateManager stateManager) {
		mAtom = (EprGroundPredicateAtom) l.getAtom();
		mEprPredicate = mAtom.mEprPredicate;
		mPolarity = l.getSign() == 1;
		mDawg = 
				dawgFactory.createOnePointDawg(
						mEprPredicate.getTermVariablesForArguments(), 
						EprHelpers.convertTermArrayToConstantList(mAtom.getArguments()));
		stateManager.registerEprGroundPredicateLiteral(this, l);
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

	@Override
	public void unregister() {
		for (ClauseEprLiteral cel : mConcernedClauseLiterals) {
			cel.unregisterIEprLiteral(this);
		}
	}

	@Override
	public void registerConcernedClauseLiteral(ClauseEprLiteral cel) {
		mConcernedClauseLiterals.add(cel);
	}
}
