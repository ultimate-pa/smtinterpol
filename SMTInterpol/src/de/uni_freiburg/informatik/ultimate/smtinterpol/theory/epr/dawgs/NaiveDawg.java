package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;

/**
 * The most naive (or rather simple) Dawg implementation I will be able to imagine.
 * A baseline for other implementations.
 * 
 * @author Alexander Nutz
 * @param <LETTER, COLNAMES>
 */
public class NaiveDawg<LETTER, COLNAMES> extends AbstractDawg<LETTER, COLNAMES> {
	
	Set<List<LETTER>> mBacking;
	private Set<List<LETTER>> mNCrossProduct;
	
	public NaiveDawg(SortedSet<COLNAMES> termVariables, Set<LETTER> allConstants, LogProxy logger) {
		super(termVariables, allConstants, logger);
		mBacking = new HashSet<List<LETTER>>();
	}

	public NaiveDawg(SortedSet<COLNAMES> termVariables, Set<LETTER> allConstants, 
			Set<List<LETTER>> initialLanguage, LogProxy logger) {
		super(termVariables, allConstants, logger);
		mBacking = new HashSet<List<LETTER>>(initialLanguage);
	}


	public NaiveDawg(NaiveDawg<LETTER, COLNAMES> nd, LogProxy logger) {
		super(nd.mColNames, nd.mAllConstants, logger);
		mBacking = new HashSet<List<LETTER>>(nd.mBacking);
	}

	public NaiveDawg(NaiveDawg<LETTER, COLNAMES> nd, Map<COLNAMES, COLNAMES> translation, LogProxy logger) {
		super(EprHelpers.applyMapping(nd.mColNames, translation), nd.mAllConstants, logger);
		mBacking = new HashSet<List<LETTER>>(nd.mBacking);
	}

	@Override
	public IDawg<LETTER, COLNAMES> join(IDawg<LETTER, COLNAMES> other) {
		// union signature
		SortedSet<COLNAMES> newSignature = new TreeSet<COLNAMES>(EprHelpers.getColumnNamesComparator());
		newSignature.addAll(this.mColNames);
		newSignature.addAll(other.getColnames());

		// intersection signature
		SortedSet<COLNAMES> commonColumns = new TreeSet<COLNAMES>(newSignature);
		commonColumns.retainAll(this.mColNames);
		commonColumns.retainAll(other.getColnames());

		NaiveDawg<LETTER, COLNAMES> otherNd = (NaiveDawg<LETTER, COLNAMES>) other;

		NaiveDawg<LETTER, COLNAMES> result = 
				new NaiveDawg<LETTER, COLNAMES>(newSignature, mAllConstants, mLogger);
		
		for (List<LETTER> pointThis : this.mBacking) {
			for (List<LETTER> pointOther : otherNd.mBacking) {
				List<LETTER> joinedPoint = new ArrayList<LETTER>(newSignature.size());
				for (COLNAMES cn : newSignature) {
					Integer thisColIndex = this.mColNameToIndex.get(cn);
					Integer otherColIndex = otherNd.mColNameToIndex.get(cn);
					if (thisColIndex != null 
							&& otherColIndex != null 
							&& pointThis.get(thisColIndex) != pointOther.get(otherColIndex)) {
						// cn is a common column and
						// the two points don't match on it
						joinedPoint = null;
						break;
					}
					LETTER lThis = thisColIndex != null ? pointThis.get(thisColIndex) : null;
					LETTER lOther = otherColIndex != null ? pointOther.get(otherColIndex) : null;
					assert lThis == null || lOther == null || lThis == lOther;
					joinedPoint.add(lThis != null ? lThis : lOther);
				}
				// if we reach here, the two points do match on all common columns
				if (joinedPoint != null) {
					result.add(joinedPoint);
				}
			}
		}
		return result;
	}

	private List<LETTER> buildJoinedPoint(List<LETTER> point1, Map<COLNAMES, Integer> colNameToIndex1,
			List<LETTER> point2, Map<COLNAMES, Integer> colNameToIndex2, SortedSet<COLNAMES> newSignature) {
		List<LETTER> result = new ArrayList<LETTER>(newSignature.size());
		for (COLNAMES cn : newSignature) {
			int index1 = colNameToIndex1.get(cn);
			LETTER l1 = point1.get(index1);
			int index2 = colNameToIndex2.get(cn);
			LETTER l2 = point2.get(index2);
			assert l1 == null || l2 == null || l1 == l2;
			if (l1 != null) {
				result.add(l1);
			} else {
				assert l2 != null;
				result.add(l2);
			}
		}
		return result;
	}


	@Override
	public IDawg<LETTER, COLNAMES> complement() {
		Set<List<LETTER>> complement = new HashSet<List<LETTER>>(getNCrossProduct());
		assert EprHelpers.verifySortsOfPoints(complement, getColnames());
		complement.removeAll(mBacking);
		NaiveDawg<LETTER, COLNAMES> result = new NaiveDawg<LETTER, COLNAMES>(mColNames, mAllConstants, complement, mLogger);
		assert EprHelpers.verifySortsOfPoints(result, getColnames());
		return result;
	}

	@Override
	public IDawg<LETTER, COLNAMES> union(IDawg<LETTER, COLNAMES> other) {
		assert other.getColnames().equals(getColnames()) : "incompatible column names";

		NaiveDawg<LETTER, COLNAMES> newDawg = 
				new NaiveDawg<LETTER, COLNAMES>(mColNames, mAllConstants, mBacking, mLogger);
		newDawg.addAll(other);

		return newDawg;
	}

	@Override
	public boolean accepts(List<LETTER> word) {
		assert mArity == word.size();
		return mBacking.contains(word);
	}

	@Override
	public void add(List<LETTER> point) {
		assert EprHelpers.verifySortsOfPoint(point, this.getColnames());
		mBacking.add(point);
	}

	@Override
	public void addAll(IDawg<LETTER, COLNAMES> other) {
		super.addAll(other);
		// assuming that we use NaiveDawgs for all Dawgs..
		NaiveDawg<LETTER, COLNAMES> naiOther = (NaiveDawg<LETTER, COLNAMES>) other;
		assert EprHelpers.verifySortsOfPoints(naiOther, getColnames());
		mBacking.addAll(naiOther.mBacking);
	}

	@Override
	public boolean isEmpty() {
		return mBacking.isEmpty();
	}

	@Override
	public boolean isUniversal() {
		return mBacking.equals(getNCrossProduct());
	}

	/**
	 * Set intersection on Dawgs. Assumes that they already share the same signature.
	 */
	@Override
	public IDawg<LETTER, COLNAMES> intersect(IDawg<LETTER, COLNAMES> other) {
		assert mColNames.equals(other.getColnames());
		NaiveDawg<LETTER, COLNAMES> naiOther = (NaiveDawg<LETTER, COLNAMES>) other;
		
		Set<List<LETTER>> newBacking = new HashSet<List<LETTER>>(mBacking);
		newBacking.retainAll(naiOther.mBacking);
		
		return new NaiveDawg<LETTER, COLNAMES>(mColNames, mAllConstants, newBacking, mLogger);
	}

	@Override
	public void removeAll(IDawg<LETTER, COLNAMES> other) {
		assert mColNames.equals(other.getColnames());
		NaiveDawg<LETTER, COLNAMES> naiOther = (NaiveDawg<LETTER, COLNAMES>) other;
		mBacking.removeAll(naiOther.mBacking);
	}
	
	private Set<List<LETTER>> getNCrossProduct() {
		if (mNCrossProduct == null) {
			mNCrossProduct = EprHelpers.computeNCrossproduct(mAllConstants, mArity, mLogger);
		}
		return mNCrossProduct;
	}

	@Override
	public boolean supSetEq(IDawg<LETTER, COLNAMES> other) {
		assert mColNames.equals(other.getColnames());
		NaiveDawg<LETTER, COLNAMES> otherNd = (NaiveDawg<LETTER, COLNAMES>) other;
		return this.mBacking.containsAll(otherNd.mBacking);
	}

	@Override
	public void addAllWithSubsetSignature(IDawg<LETTER, COLNAMES> other) {
		assert mColNames.containsAll(other.getColnames());
		NaiveDawg<LETTER, COLNAMES> nd = (NaiveDawg<LETTER, COLNAMES>) other;
		//TODO: could be done nicer --> only go through the points that actually occur in this.mBacking..
		for (List<LETTER> pt : nd.mBacking) {
			addWithSubsetSignature(pt, nd.mColNames);
		}
	}

	@Override
	public void removeAllWithSubsetSignature(IDawg<LETTER, COLNAMES> other) {
		assert mColNames.containsAll(other.getColnames());
		NaiveDawg<LETTER, COLNAMES> nd = (NaiveDawg<LETTER, COLNAMES>) other;
		//TODO: could be done nicer --> only go through the points that actually occur in this.mBacking..
		for (List<LETTER> pt : nd.mBacking) {
			mBacking.removeAll(blowUpForCurrentSignature(pt, nd.mColNames, mColNames, mAllConstants));
		}
	}

	private static <LETTER, COLNAMES> List<List<LETTER>> blowUpForCurrentSignature(
			List<LETTER> pt, SortedSet<COLNAMES> ptSig, 
			SortedSet<COLNAMES> targetSig, Set<LETTER> allConstants) {
		assert targetSig.containsAll(ptSig);
		assert pt.size() == ptSig.size();
		List<List<LETTER>> result = new ArrayList<List<LETTER>>();
		result.add(new ArrayList<LETTER>());
		for (COLNAMES cn : targetSig) {
			//TODO hacky
			int posInPtSig = -1;
			Iterator<COLNAMES> ptSigIt = ptSig.iterator();
			for (int i = 0; i < ptSig.size(); i++) {
				if (ptSigIt.next() == cn) {
					posInPtSig = i;
				}
			}
			
			List<List<LETTER>> newResult = new ArrayList<List<LETTER>>();
			for (List<LETTER> prefix : result) {

				if (posInPtSig != -1) {
					ArrayList<LETTER> newPrefix = new ArrayList<LETTER>(prefix);
					newPrefix.add(pt.get(posInPtSig));
					newResult.add(newPrefix);
				} else {
					for (LETTER c : allConstants) {
						ArrayList<LETTER> newPrefix = new ArrayList<LETTER>(prefix);
						newPrefix.add(c);
						newResult.add(newPrefix);
					}
				}
			}

			result = newResult;
		}
		return result;
	}

	@Override
	public IDawg<LETTER, COLNAMES> select(Map<COLNAMES, LETTER> selectMap) {
		assert mColNames.containsAll(selectMap.keySet());
		Set<List<LETTER>> newBacking = new HashSet<List<LETTER>>(mBacking);
		for (List<LETTER> word : mBacking) {
			for (Entry<COLNAMES, LETTER> en : selectMap.entrySet()) {
				int index = mColNameToIndex.get(en.getKey());
				if (word.get(index) != en.getValue()) {
					newBacking.remove(word);
				}
			}
		}
		return new NaiveDawg<LETTER, COLNAMES>(mColNames, mAllConstants, newBacking, mLogger);
	}

	@Override
	protected Iterable<List<LETTER>> listPoints() {
		return mBacking;
	}

	@Override
	public Iterator<List<LETTER>> iterator() {
		return mBacking.iterator();
	}

	@Override
	public boolean isSingleton() {
		return mBacking.size() == 1;
	}

	public void addWithSubsetSignature(List<LETTER> point, SortedSet<COLNAMES> sig) {
		mBacking.addAll(blowUpForCurrentSignature(point, sig, mColNames, mAllConstants));
	}
}
