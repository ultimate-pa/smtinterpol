package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;

public class DawgSignature<COLNAMES> {
	
	private SortedSet<COLNAMES> mColNames;
	private Map<COLNAMES, Integer> mColNameToIndex;
	private Map<COLNAMES, Object> mColnameToSortId;
	private List<Object> mColumnSorts;
	
	public DawgSignature(SortedSet<COLNAMES> colNames) {
		mColNames = colNames;
		
		Map<COLNAMES, Object> colnameToSortId = new HashMap<COLNAMES, Object>();
		mColNameToIndex = new HashMap<COLNAMES, Integer>();
		List<Object> columnSorts = new ArrayList<Object>();
		Iterator<COLNAMES> it = mColNames.iterator();
		for (int i = 0; i < mColNames.size(); i++) {
			COLNAMES cn = it.next();
			mColNameToIndex.put(cn, i);
			Object cnSort = EprHelpers.extractSortFromColname(cn);
			colnameToSortId.put(cn, cnSort);
			columnSorts.add(cnSort);
		}
		
		mColumnSorts = Collections.unmodifiableList(columnSorts);
		mColnameToSortId = Collections.unmodifiableMap(colnameToSortId);
	}

	public Map<COLNAMES, Integer> getColNameToIndex() {
		return mColNameToIndex;
	}

	public SortedSet<COLNAMES> getColNames() {
		return mColNames;
	}

	public Object getSortForColname(COLNAMES colName) {
		return mColnameToSortId.get(colName);
	}

	public List<Object> getColumnSorts() {
		return mColumnSorts;
	}

	public int size() {
		return mColNames.size();
	}

}
