package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;

public abstract class AbstractDawg<LETTER, COLNAMES> implements IDawg<LETTER, COLNAMES> {
	
	protected final int mArity;
	
	/**
	 * Store the column names in a list. By convention this list has no repetitions. 
	 *  -- we don't use a (sorted) set for this because we store our points in lists
	 */
//	protected final List<COLNAMES> mColNames;
//	protected final COLNAMES[] mColNames;
	protected final SortedSet<COLNAMES> mColNames;
	protected final Set<LETTER> mAllConstants;
	protected final Map<COLNAMES, Integer> mColNameToIndex;
	
//	public AbstractDawg(List<COLNAMES> colNames, Set<LETTER> allConstants) {
	public AbstractDawg(SortedSet<COLNAMES> colNames, Set<LETTER> allConstants) {
//		assert hasNoRepetitions(colNames) : "convention: we only allow dawgs whose signature has no "
//				+ "repetitions -- if it had repetitions, we would just omit one column "
//				+ "(..and select the matching points only)";
		mColNames = colNames;
		mArity = colNames.size();
		mAllConstants = allConstants;
		
		mColNameToIndex = new HashMap<COLNAMES, Integer>();
		Iterator<COLNAMES> it = mColNames.iterator();
		for (int i = 0; i < mColNames.size(); i++) {
			COLNAMES cn = it.next();
			mColNameToIndex.put(cn, i);
		}
	}

	private boolean hasNoRepetitions(List<COLNAMES> colNames) {
		for (int i = 0; i < colNames.size(); i++) {
			for (int j = 0; j < i; j++) {
				if (colNames.get(j).equals(colNames.get(i))) {
					return false;
				}
			}
		}
		return true;
	}

	@Override
//	public List<COLNAMES> getColnames() {
	public SortedSet<COLNAMES> getColnames() {
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
