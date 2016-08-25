package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public abstract class AbstractDawg<LETTER, COLNAMES> implements IDawg<LETTER, COLNAMES> {
	
	protected final int mArity;
	protected final COLNAMES[] mColNames;
	protected final Set<LETTER> mAllConstants;
	
	public AbstractDawg(COLNAMES[] termVariables, Set<LETTER> allConstants) {
		mColNames = termVariables;
		mArity = termVariables.length;
		mAllConstants = allConstants;
	}

	@Override
	public COLNAMES[] getColnames() {
		return mColNames;
	}
	
	@Override
	public int getArity() {
		return mArity;
	}
}
