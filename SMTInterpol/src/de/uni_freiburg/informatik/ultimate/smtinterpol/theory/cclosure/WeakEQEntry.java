/*
 * Copyright (C) 2014 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

/**
 * An entry in the weak equivalence (modulo i) graph map.  This entries stores
 * for every index i the store that introduces the store edge on the path.
 * @author Juergen Christ
 */
public class WeakEQEntry {
	
	static class EntryPair {
		private final CCTerm mLeft;
		private final CCTerm mRight;
		
		public EntryPair(CCTerm store) {
			mLeft = mRight = store;
		}
		
		public EntryPair(CCTerm left, CCTerm right) {
			mLeft = left;
			mRight = right;
		}
		
		public EntryPair(EntryPair toSwap) {
			mLeft = toSwap.mRight;
			mRight = toSwap.mLeft;
		}
		
		public EntryPair(CCTerm left, CCTerm right, boolean inOrder) {
			if (inOrder) {
				mLeft = left;
				mRight = right;
			} else {
				mLeft = right;
				mRight = left;
			}
		}
		
		public CCTerm getLeft() {
			return mLeft;
		}
		
		public CCTerm getRight() {
			return mRight;
		}
		
		public CCTerm getEntry(boolean inOrder) { // NOPMD
			return inOrder ? mLeft : mRight;
		}
		
		public String toString() {
			return "(" + mLeft + "," + mRight + ")";
		}
	}
	
	private Map<CCTerm, EntryPair> mEntries;
	
	private Map<CCTerm, WeakEQiEntry> mModuloEntries;

	private EntryPair mDefault;
	
	//@invariant mDefault != null ==> mEntries != null;
	
	public WeakEQEntry() {
		mDefault = null;
	}
	
	/**
	 * Add a store to the graph.  This operation is assumed to be done before
	 * any merging occurs.  It initializes the weak equivalence edges according
	 * to the following observation:
	 * <ol>
	 * <li>The first store sets the default value but specifies that no path
	 * exists for the index of the store by mapping the index to
	 * <code>null</code>.</li>
	 * <li>A store to a different index updates the path information for the
	 * index of the first index to go through the second store.</li>
	 * <li>A store to a third index different from any previous entry is ignored
	 * since the graph is already fully connected.
	 * @param store The store to add.
	 * @return Did we change something?
	 */
	public boolean addStore(CCTerm store) {
		CCTerm repidx = ArrayTheory.getIndexFromStore(store).getRepresentative();
		if (mDefault == null) {
			assert mEntries == null;
			mDefault = new EntryPair(store);
			mEntries = new HashMap<CCTerm, EntryPair>();
			mEntries.put(repidx, null);
			assert defaultInvariant();
			return true;
		} else {
			Entry<CCTerm, EntryPair> e = mEntries.entrySet().iterator().next();
			if (e.getValue() == null && e.getKey() != repidx) {
				e.setValue(new EntryPair(store));
				assert defaultInvariant();
				return true;
			}
		}
		assert defaultInvariant();
		// Ignore otherwise since we are already fully connected.
		return false;
	}
	
	/**
	 * Merge two entries into this entry.  We distinguish between two cases:
	 * <ul>
	 * <li>If we merge into an empty entry, we basically have to copy the
	 * information from the left entry.  If the right entry prevents a path, we
	 * still have to prevent this path.  Otherwise, we have to set the path
	 * information to the default of the left entry.</li>
	 * <li>If we merge into an existing entry, we only have to check if a path
	 * that currently does not exist (i.e. it is mapped to <code>null</code>)
	 * can be replaced by a path through the left and the right entries.  To
	 * have all stores along this path, we can nevertheless merge all entries
	 * from the left and the right side into the current entry.</li>
	 * </ul>
	 * @param left         The first part of the path.
	 * @param leftInOrder  Is the left entry in the expected order?
	 * @param right        The second part of the path.
	 * @param rightInOrder Is the right entry in the expected order?
	 * @param thisInOrder  Is this entry in the expected order?
	 * @return Did we change something?
	 */
	public boolean merge(WeakEQEntry left, boolean leftInOrder,
			WeakEQEntry right, boolean rightInOrder, boolean thisInOrder) {
		boolean result = false;
		if (mDefault == null) {
			result = true;
			assert mEntries == null;
			CCTerm aToB = left.mDefault.getEntry(leftInOrder);
			CCTerm cToB = right.mDefault.getEntry(!rightInOrder);
			mDefault = new EntryPair(aToB, cToB, thisInOrder);
			mEntries = new HashMap<CCTerm, EntryPair>();
			for (Entry<CCTerm, EntryPair> e : left.mEntries.entrySet()) {
				if (e.getValue() == null) {
					mEntries.put(e.getKey(), null);
					continue;
				}
				EntryPair re = right.getConnection(e.getKey());
				if (re == null) {
					mEntries.put(e.getKey(), null);
					continue;
				}
				aToB = e.getValue().getEntry(leftInOrder);
				cToB = re.getEntry(!rightInOrder);
				mEntries.put(e.getKey(), new EntryPair(aToB, cToB, thisInOrder));
			}
			for (Entry<CCTerm, EntryPair> e : right.mEntries.entrySet()) {
				if (mEntries.containsKey(e.getKey()))
					continue;
				if (e.getValue() == null) {
					mEntries.put(e.getKey(), null);
					continue;
				}
				EntryPair le = left.getConnection(e.getKey());
				if (le == null) {
					mEntries.put(e.getKey(), null);
					continue;
				}
				aToB = le.getEntry(leftInOrder);
				cToB = e.getValue().getEntry(!rightInOrder);
				mEntries.put(e.getKey(), new EntryPair(aToB, cToB, thisInOrder));
			}
		} else {
			// Merge into existing entry
			assert mEntries != null;
			for (Entry<CCTerm, EntryPair> e : mEntries.entrySet()) {
				if (e.getValue() == null) {
					CCTerm idx = e.getKey();
					EntryPair l = left.getConnection(idx);
					EntryPair r = right.getConnection(idx);
					if (l != null && r != null) {
						CCTerm aToB = l.getEntry(leftInOrder);
						CCTerm cToB = r.getEntry(!rightInOrder);
						e.setValue(new EntryPair(aToB, cToB, thisInOrder));
						result = true;
					}
				}
			}
			// FIXME We need to propagate the store indices or collect them otherwise for weakeq-ext
//			for (CCTerm store : left.mEntries.keySet()) {
//				if (!mEntries.containsKey(store))
//					mEntries.put(store, mDefault);
//			}
//			for (CCTerm store : right.mEntries.keySet()) {
//				if (!mEntries.containsKey(store))
//					mEntries.put(store, mDefault);
//			}
		}
		assert defaultInvariant();
		return result;
	}
	
	public EntryPair getConnection(CCTerm index) {
		CCTerm repidx = index.getRepresentative();
		if (mEntries != null && mEntries.containsKey(repidx))
			return mEntries.get(repidx);
		return mDefault;
	}
	
	Map<CCTerm, EntryPair> getEntries() {
		return mEntries;
	}
	
	EntryPair getDefault() {
		return mDefault;
	}

	public void addModEdge(CCTerm idx, WeakEQiEntry modi) {
		if (mModuloEntries == null)
			mModuloEntries = new HashMap<CCTerm, WeakEQiEntry>();
		mModuloEntries.put(idx.getRepresentative(), modi);
	}
	
	public WeakEQiEntry getModuloPath(CCTerm index) {
		if (mModuloEntries == null)
			return null;
		return mModuloEntries.get(index.getRepresentative());
	}
	
	Map<CCTerm, WeakEQiEntry> getModuloEdges() {
		return mModuloEntries;
	}
	
	public String toString() {
		if (mDefault == null)
			return "no path";
		StringBuilder sb = new StringBuilder();
		if (mEntries != null) {
			for (Map.Entry<CCTerm, EntryPair> path : mEntries.entrySet())
				sb.append('[').append(path.getKey()).append("=>").append(
						path.getValue()).append(']');
		}
		sb.append("[=>").append(mDefault).append(']');
		if (mModuloEntries != null) {
			for (Entry<CCTerm, WeakEQiEntry> path : mModuloEntries.entrySet())
				sb.append("[[").append(path.getKey()).append("=>").append(
						path.getValue()).append("]]");
		}
		return sb.toString();
	}
	
	private boolean checkCongruenceArray(CCTerm arr, CCTerm store) {
		CCTerm storearray =
				ArrayTheory.getArrayFromStore(store).getRepresentative();
		return arr == store.getRepresentative() || arr == storearray;
	}
	
	private boolean checkCongruence(CCTerm left, CCTerm right, EntryPair store) {
		return checkCongruenceArray(left, store.getLeft())
				&& checkCongruenceArray(right, store.getRight());
	}
	
	// For every EntryPair: mLeft is associated with lower and mRight with
	// bigger array
	boolean invariant(CCTerm left, CCTerm right) {
		assert left == left.getRepresentative();
		assert right == right.getRepresentative();
		if (left.mArrayNum > right.mArrayNum) {
			CCTerm tmp = left;
			left = right;
			right = tmp;
		}
		if (mDefault != null) {
			for (Entry<CCTerm, EntryPair> path : mEntries.entrySet())
				if (path.getValue() != null) {
					assert checkCongruence(left, right, path.getValue())
						: "Error on idx " + path.getKey();
					assert path.getKey().getRepresentative() != ArrayTheory.getIndexFromStore(path.getValue().getLeft());
					assert path.getKey().getRepresentative() != ArrayTheory.getIndexFromStore(path.getValue().getRight());
				}
			assert checkCongruence(left, right, mDefault);
		}
		return true;
	}
	
	boolean defaultInvariant() {
		assert mEntries.containsKey(ArrayTheory.getIndexFromStore(
				mDefault.getLeft()).getRepresentative());
		assert mEntries.containsKey(ArrayTheory.getIndexFromStore(
				mDefault.getRight()).getRepresentative());
		return true;
	}
}
