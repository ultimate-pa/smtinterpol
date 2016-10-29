package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;

/**
 * Contains stuff that is expected to be common to all Dawg implementations.
 * 
 * @author Alexander Nutz
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public abstract class AbstractDawg<LETTER, COLNAMES> implements IDawg<LETTER, COLNAMES> {
	
	protected final int mArity;
	protected final LogProxy mLogger;
	
	/**
	 * Store the column names in a list. By convention this list has no repetitions. 
	 *  -- we don't use a (sorted) set for this because we store our points in lists
	 */
	protected final SortedSet<COLNAMES> mColNames;
	protected final Set<LETTER> mAllConstants;
	protected final Map<COLNAMES, Integer> mColNameToIndex;
	
	public AbstractDawg(SortedSet<COLNAMES> colNames, Set<LETTER> allConstants, LogProxy logger) {
		mColNames = colNames;
		mArity = colNames.size();
		mAllConstants = allConstants;
		mLogger = logger;
		
		mColNameToIndex = new HashMap<COLNAMES, Integer>();
		Iterator<COLNAMES> it = mColNames.iterator();
		for (int i = 0; i < mColNames.size(); i++) {
			COLNAMES cn = it.next();
			mColNameToIndex.put(cn, i);
		}
	}

	@Override
	public SortedSet<COLNAMES> getColnames() {
		return mColNames;
	}
	
	@Override
	public int getArity() {
		return mArity;
	}

	
	@Override
	public void addAll(IDawg<LETTER, COLNAMES> dawg) {
		assert mColNames.equals(dawg.getColnames());
	}

	@Override
	public String toString() {
//		int colWidth = -1;
//		for (COLNAMES cn : getColnames()) {
//			colWidth = colWidth < cn.toString().length() ? cn.toString().length() : colWidth;
//		}
//		colWidth += 2;

		int displayLength = 20;

		StringBuilder sb = new StringBuilder();

		sb.append("<");
		String comma = "";
		for (COLNAMES cn : getColnames()) {
			sb.append(comma);
			
			String cns = cn.toString();
			if (cns.contains("AUX")) {
				cns = "(AUX ...)";
			}
			sb.append(cns);
			comma = ", ";
		}
		sb.append(">  ");
		
		for (List<LETTER> pt : this.listPoints()) {
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

	/**
	 * Lists the language of this dawg word by word
	 * @return
	 */
	protected abstract Iterable<List<LETTER>> listPoints() ;
}
