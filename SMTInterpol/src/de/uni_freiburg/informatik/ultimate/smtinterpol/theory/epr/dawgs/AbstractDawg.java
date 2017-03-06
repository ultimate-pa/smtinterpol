/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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

import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;

/**
 * 
 * 
 * @author Alexander Nutz
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public abstract class AbstractDawg<LETTER, COLNAMES> implements IDawg<LETTER, COLNAMES> {
	
//	protected final int mArity;
	protected final LogProxy mLogger;

//	private final Map<COLNAMES, Object> mColnameToSortId = new HashMap<COLNAMES, Object>();
//	
//	/**
//	 * Store the column names in a list. By convention this list has no repetitions. 
//	 *  -- we don't use a (sorted) set for this because we store our points in lists
//	 */
//	protected final SortedSet<COLNAMES> mColNames;
//	protected final Map<COLNAMES, Integer> mColNameToIndex;
	
	protected final DawgSignature<COLNAMES> mSignature;
	
	public Map<COLNAMES, Integer> getColNameToIndex() {
		return mSignature.getColNameToIndex();
	}

	public AbstractDawg(SortedSet<COLNAMES> colNames, LogProxy logger) {
		mSignature = new DawgSignature<COLNAMES>(colNames);
//		mArity = colNames.size();
		mLogger = logger;

	}
	
	@Override
	public DawgSignature<COLNAMES> getSignature() {
		return mSignature;
	}

	@Override
	public SortedSet<COLNAMES> getColNames() {
		return mSignature.getColNames();
	}
	
	public Object getSortForColname(COLNAMES colName) {
		return mSignature.getSortForColname(colName);
	}
	
	@Override
	public String toString() {
		int displayLength = 20;

		StringBuilder sb = new StringBuilder();

		sb.append("<");
		String comma = "";
		for (COLNAMES cn : getColNames()) {
			sb.append(comma);
			
			String cns = cn.toString();
			if (cns.contains("AUX")) {
				cns = "(AUX ...)";
			}
			sb.append(cns);
			comma = ", ";
		}
		sb.append(">  ");
		
		for (List<LETTER> pt : this.getAllPointsSorted()) {
//			for (LETTER ltr : pt) {
//				sb.append(String.format("%10s", ltr));
//			}
//			sb.append("\n");
//			if (sb.length() < displayLength) {
			if (displayLength > 0) {
				sb.append(pt);
				displayLength -= pt.toString().length();
			}
		}
		if (displayLength <= 0) {
			sb.append("..");
		}
		return sb.toString();
	}
}
