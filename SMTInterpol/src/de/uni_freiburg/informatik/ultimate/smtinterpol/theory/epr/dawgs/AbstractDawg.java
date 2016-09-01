package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public abstract class AbstractDawg<LETTER, COLNAMES> implements IDawg<LETTER, COLNAMES> {
	
	protected final int mArity;
//	protected final COLNAMES[] mColNames;
//	protected final SortedSet<COLNAMES> mColNames;
	protected final List<COLNAMES> mColNames;
	protected final Set<LETTER> mAllConstants;
	protected final Map<COLNAMES, Integer> mColNameToIndex;
	
	public AbstractDawg(List<COLNAMES> termVariables, Set<LETTER> allConstants) {
//	public AbstractDawg(SortedSet<COLNAMES> termVariables, Set<LETTER> allConstants) {
		mColNames = termVariables;
//		mArity = termVariables.length;
		mArity = termVariables.size();
		mAllConstants = allConstants;
		
		mColNameToIndex = new HashMap<COLNAMES, Integer>();
		for (int i = 0; i < mColNames.size(); i++) {
			mColNameToIndex.put(mColNames.get(i), i);
		}
	}

	@Override
	public List<COLNAMES> getColnames() {
//	public SortedSet<COLNAMES> getColnames() {
		return mColNames;
	}
	
	@Override
	public int getArity() {
		return mArity;
	}
	
	@Override
	public void addAll(IDawg<LETTER, COLNAMES> dawg) {
//		assert Arrays.equals(mColNames, dawg.getColnames());
		assert mColNames.equals(dawg.getColnames());
	}

//	@Override
//	public void addAllWithSubsetSignature(IDawg<LETTER, COLNAMES> d1) {
//		
//	}
	
	
}
