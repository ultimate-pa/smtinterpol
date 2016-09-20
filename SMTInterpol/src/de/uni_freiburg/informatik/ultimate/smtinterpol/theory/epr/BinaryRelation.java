package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

public class BinaryRelation<T, U> {

	private final Map<T, Set<U>> mBacking = new HashMap<T, Set<U>>();

	public void addPair(T t, U u) {
        Set<U> set = mBacking.get(t);
		if (set == null) {
			set = new HashSet<U>();
			mBacking.put(t, set);
		}
		set.add(u);
	}
	
	public Set<T> getDomain() {
		return mBacking.keySet();
	}
	
	public Set<U> getImage(T t) {
		return mBacking.get(t);
	}
	
	/**
	 * Checks if the represented relation is "rechtseindeutig" (right-unique?)
	 *  (strictly speaking this checks if it is a partial function)
	 * @return
	 */
	public boolean isFunction() {
		for (Entry<T, Set<U>> en : mBacking.entrySet()) {
			if (en.getValue().size() > 1) {
				return false;
			}
		}
		return true;
	}
	
	public Map<T, U> getFunction() {
		assert isFunction();
		Map<T, U> result =  new HashMap<T, U>();
		
		for (Entry<T, Set<U>> en : mBacking.entrySet()) {
			assert en.getValue().size() == 1 : "no function";
			result.put(en.getKey(), en.getValue().iterator().next());
		}
		return result;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (Entry<T, Set<U>> en : mBacking.entrySet()) {
			for (U el : en.getValue()) {
				sb.append("(" + en.getKey() + ", " + el + ") ");
			}
		}
//		return mBacking.toString();
		return sb.toString();
	}
}
