/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Util Library.
 * 
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Util Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.EmptyDawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Triple;

import java.util.NoSuchElementException;
import java.util.Set;

/**
 * Represents the transition relation of a deterministic dawg.
 * 
 * Adapted from NestedMap2 from the Ultimate Util library from the Ultimate framework.
 * 
 * @author Matthias Heizmann
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <K1>
 * @param <K2>
 * @param <V>
 */
public class DeterministicDawgTransitionRelation<K1, K2, V> {
	
	private final Map<K1, Map<K2, V>> mK1ToK2ToV = new HashMap<K1, Map<K2, V>>();
	
	/**
	 * standard constructor, constructs empty relation
	 */
	public DeterministicDawgTransitionRelation() {
		// do nothing
	}
	
	/**
	 * copy constructor
	 * 
	 * @param orig
	 */
	public DeterministicDawgTransitionRelation(DeterministicDawgTransitionRelation<K1, K2, V> orig) {
		for (Entry<K1, Map<K2, V>> en1 : orig.mK1ToK2ToV.entrySet()) {
			final Map<K2, V> innerMap = new HashMap<K2, V>();
			mK1ToK2ToV.put(en1.getKey(), innerMap);
			for (Entry<K2, V> en2 : orig.mK1ToK2ToV.get(en1.getKey()).entrySet()) {
				innerMap.put(en2.getKey(), en2.getValue());
			}
		}
	}
	
	public V put(final K1 key1, final K2 key2, final V value) {
		assert !(key2 instanceof EmptyDawgLetter<?, ?>) : "edges that are labelled with the empty letter should be omitted; "
				+ "catch this case outside";
		Map<K2, V> k2toV = mK1ToK2ToV.get(key1);
		if (k2toV == null) {
			k2toV = new HashMap<K2, V>();
			mK1ToK2ToV.put(key1, k2toV);
		}
		assert !k2toV.containsKey(key2) || k2toV.get(key2).equals(value) : 
			"we don't expect that put overwrites something, here --> catch this case outside!";
		return k2toV.put(key2, value);
	}
	
	public V get(final K1 key1, final K2 key2) {
		final Map<K2, V> k2toV = mK1ToK2ToV.get(key1);
		if (k2toV == null) {
			return null;
		} else {
			return k2toV.get(key2);
		}
	}
	
	public Map<K2,V> get(final K1 key1) {
		return mK1ToK2ToV.get(key1);
	}
	
	public Set<K1> keySet() {
		return mK1ToK2ToV.keySet();
	}
	
	public Iterable<Pair<K1,K2>> keys2() {
		return new Iterable<Pair<K1,K2>>() {

			@Override
			public Iterator<Pair<K1, K2>> iterator() {
				return new Iterator<Pair<K1,K2>>() {
					private Iterator<Entry<K1, Map<K2, V>>> mIterator1;
					private Entry<K1, Map<K2, V>> mIterator1Object;
					private Iterator<K2> mIterator2;

					{
						mIterator1 = mK1ToK2ToV.entrySet().iterator();
						if (mIterator1.hasNext()) {
							mIterator1Object = mIterator1.next();
							mIterator2 = mIterator1Object.getValue().keySet().iterator();
						}
					}

					@Override
					public boolean hasNext() {
						if (mIterator1Object == null) {
							return false;
						} else {
							return mIterator2.hasNext();
						}
					}

					@Override
					public Pair<K1, K2> next() {
						if (mIterator1Object == null) {
							throw new NoSuchElementException();
						} else {
							if (!mIterator2.hasNext()) {
								if (!mIterator1.hasNext()) {
									throw new NoSuchElementException();
								} else {
									mIterator1Object = mIterator1.next();
									assert mIterator1Object.getValue().size() > 0 : "must contain at least one value";
									mIterator2 = mIterator1Object.getValue().keySet().iterator();
								}
							}
							return new Pair<K1, K2>(mIterator1Object.getKey(), mIterator2.next());
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException("not yet implemented");
					}
				};
			}
		};
		
	}
	
	//TODO more efficient iterable
	public Iterable<Triple<K1,K2,V>> entrySet() {
		final ArrayList<Triple<K1,K2,V>> result = new ArrayList<Triple<K1,K2,V>>();
		for (final Entry<K1, Map<K2, V>> entryOuter  : mK1ToK2ToV.entrySet()) {
			for (final Entry<K2, V> entryInner : entryOuter.getValue().entrySet()) {
				result.add(new Triple<K1,K2,V>(entryOuter.getKey(), entryInner.getKey(), entryInner.getValue()));
			}
		}
		return result;
	}

	public void addAll(final DeterministicDawgTransitionRelation<K1, K2, V> nestedMap) {
		for (final Triple<K1, K2, V> triple : nestedMap.entrySet()) {
			this.put(triple.getFirst(), triple.getSecond(), triple.getThird());
		}
	}
	
	public Map<K2, V> remove(final K1 k1) {
		return mK1ToK2ToV.remove(k1);
	}
	
	public V remove(final K1 k1, final K2 k2) {
		final Map<K2, V> k2ToV = mK1ToK2ToV.get(k1);
		if (k2ToV == null) {
			return null;
		} else {
			return k2ToV.remove(k2);
		}
	}

	@Override
	public String toString() {
//		return mK1ToK2ToV.toString();
		final StringBuilder sb = new StringBuilder();
		for (Triple<K1, K2, V> edge : this.entrySet()) {
			sb.append(edge + "\n");
		}
		return sb.toString();
	}
	
	public void clear() {
		mK1ToK2ToV.clear();
	}
	
	public int size() {
		int result = 0;
		for (final Entry<K1, Map<K2, V>> entry : mK1ToK2ToV.entrySet()) {
			result += entry.getValue().size();
		}
		return result;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mK1ToK2ToV == null) ? 0 : mK1ToK2ToV.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		final DeterministicDawgTransitionRelation other = (DeterministicDawgTransitionRelation) obj;
		if (mK1ToK2ToV == null) {
			if (other.mK1ToK2ToV != null)
				return false;
		} else if (!mK1ToK2ToV.equals(other.mK1ToK2ToV))
			return false;
		return true;
	}

//	public DeterministicDawgTransitionRelation<K1, K2, V> copy() {
//		final DeterministicDawgTransitionRelation<K1, K2, V> result = new DeterministicDawgTransitionRelation<K1, K2, V>();
//		for (final K1 k1 : this.keySet()) {
//			result.mK1ToK2ToV.put(k1, new HashMap<K2, V>(this.get(k1)));
//		}
//		return result;
//	}
	
	public boolean isEmpty() {
		return mK1ToK2ToV.isEmpty();
	}

	/**
	 * Retrieves all the incoming edges for one state.
	 * TODO: this implementation is rather inefficient, 
	 *   one could introduce additional "backwards"-HashMaps to speed this up..
	 *   
	 * @param stateLeft
	 * @return
	 */
	public Set<Pair<K1, K2>> getInverse(DawgState stateLeft) {
		Set<Pair<K1, K2>> result = new HashSet<Pair<K1,K2>>();
		for (Entry<K1, Map<K2, V>> en1 : mK1ToK2ToV.entrySet()) {
			for (Entry<K2, V> en2 : en1.getValue().entrySet()) {
				if (en2.getValue().equals(stateLeft)) {
					result.add(new Pair<K1, K2>(en1.getKey(), en2.getKey()));
				}
			}
		}
		return result;
	}

	public Set<Pair<K2, V>> getOutEdgeSet(K1 state) {
		Map<K2, V> innerMap = mK1ToK2ToV.get(state);
		if (innerMap == null) {
			return Collections.emptySet();
		} else {
			Set<Pair<K2, V>> result = new HashSet<Pair<K2,V>>();
			for (Entry<K2, V> en : innerMap.entrySet()) {
				result.add(new Pair<K2, V>(en.getKey(), en.getValue()));
			}
			return result;
		}
	}
	
	
	
}