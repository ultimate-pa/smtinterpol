/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
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

	private final SortedSet<COLNAMES> mColNames;
	private final Map<COLNAMES, Integer> mColNameToIndex;
	private final Map<COLNAMES, Object> mColnameToSortId;
	private final List<Object> mColumnSorts;

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
		assert mColNames.contains(colName);
		Object result = mColnameToSortId.get(colName);
		assert result != null;
		return result;
	}

	public List<Object> getColumnSorts() {
		return mColumnSorts;
	}

	public int getNoColumns() {
		return mColNames.size();
	}

	public int size() {
		return mColNames.size();
	}

	@Override
	public boolean equals(Object other) {
		if (!(other instanceof DawgSignature<?>)) {
			return false;
		}

		return ((DawgSignature<?>) other).getColNames().equals(mColNames);
	}

	@Override
	public String toString() {
		return "DawgSignature: " + mColNames.toString();
	}
}
