package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;

/**
 * The most naive (or rather simple) Dawg implementation I will be able to imagine.
 * A baseline for other implementations.
 * 
 * @author nutz
 * @param <LETTER, COLNAMES>
 */
public class NaiveDawg<LETTER, COLNAMES> extends AbstractDawg<LETTER, COLNAMES> {
	
	Set<List<LETTER>> mBacking;
	private Set<List<LETTER>> mNCrossProduct;
	
	public NaiveDawg(SortedSet<COLNAMES> termVariables, Set<LETTER> allConstants) {
		super(termVariables, allConstants);
		mBacking = new HashSet<List<LETTER>>();
	}

	public NaiveDawg(SortedSet<COLNAMES> termVariables, Set<LETTER> allConstants, 
			Set<List<LETTER>> initialLanguage) {
		super(termVariables, allConstants);
		mBacking = new HashSet<List<LETTER>>(initialLanguage);
	}


	public NaiveDawg(NaiveDawg<LETTER, COLNAMES> nd) {
		super(nd.mColNames, nd.mAllConstants);
		mBacking = new HashSet<List<LETTER>>(nd.mBacking);
	}

//	public NaiveDawg(NaiveDawg<LETTER, COLNAMES> nd, DawgTranslation<COLNAMES> translation) {
	public NaiveDawg(NaiveDawg<LETTER, COLNAMES> nd, Map<COLNAMES, COLNAMES> translation) {
		super(EprHelpers.applyMapping(nd.mColNames, translation), nd.mAllConstants);
		mBacking = new HashSet<List<LETTER>>(nd.mBacking);
	}

//	public NaiveDawg(IDawg<LETTER, COLNAMES> other, Map<COLNAMES, Term> translation) {
//		// TODO Auto-generated constructor stub
//	}

	@Override
	public IDawg<LETTER, COLNAMES> join(IDawg<LETTER, COLNAMES> other) {
		
		// union signature
//		Map<COLNAMES, Integer> reverseMap = new HashMap<COLNAMES, Integer>();
//		List<COLNAMES> newSignature = new ArrayList<COLNAMES>();
//		SortedSet<COLNAMES> newSignature = new TreeSet<COLNAMES>();
////		SortedSet<COLNAMES> newSignature = new TreeSet<COLNAMES>();
//		for (int i = 0; i < this.getColnames().size(); i++) {
//			newSignature.add(this.getColnames().get(i));
////			reverseMap.put(this.getColnames().get(i), i);
//		}
		SortedSet<COLNAMES> newSignature = new TreeSet<COLNAMES>(EprHelpers.getColumnNamesComparator());
		newSignature.addAll(this.mColNames);
		newSignature.addAll(other.getColnames());

		// intersection signature
		SortedSet<COLNAMES> commonColumns = new TreeSet<COLNAMES>(newSignature);
		commonColumns.retainAll(this.mColNames);
		commonColumns.retainAll(other.getColnames());

//		for (COLNAMES cn : other.getColnames()) {
//			if (!newSignature.contains(cn)) {
//				newSignature.add(cn);
//			} else {
//				commonColumns.add(cn);
//			}
//		}
		
		NaiveDawg<LETTER, COLNAMES> otherNd = (NaiveDawg<LETTER, COLNAMES>) other;

		NaiveDawg<LETTER, COLNAMES> result = 
				new NaiveDawg<LETTER, COLNAMES>(newSignature, mAllConstants);
		
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
//				result.add(buildJoinedPoint(pointThis, this.mColNameToIndex, pointOther, otherNd.mColNameToIndex, newSignature));
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
		complement.removeAll(mBacking);
		return new NaiveDawg<LETTER, COLNAMES>(mColNames, mAllConstants, complement);
	}

	@Override
	public IDawg<LETTER, COLNAMES> union(IDawg<LETTER, COLNAMES> other) {
		assert other.getColnames().equals(getColnames()) : "incompatible column names";

		NaiveDawg<LETTER, COLNAMES> newDawg = 
				new NaiveDawg<LETTER, COLNAMES>(mColNames, mAllConstants, mBacking);
		newDawg.addAll(other);

		return newDawg;
	}

	@Override
	public boolean accepts(LETTER[] point) {
		return mBacking.contains(Arrays.asList(point));
	}

	@Override
	public void add(List<LETTER> point) {
		mBacking.add(point);
	}

	@Override
	public void addAll(IDawg<LETTER, COLNAMES> other) {
		// assuming that we use NaiveDawgs for all Dawgs..
		NaiveDawg<LETTER, COLNAMES> naiOther = (NaiveDawg<LETTER, COLNAMES>) other;
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
		
		return new NaiveDawg<LETTER, COLNAMES>(mColNames, mAllConstants, newBacking);
	}

	@Override
	public void removeAll(IDawg<LETTER, COLNAMES> other) {
		assert mColNames.equals(other.getColnames());
		NaiveDawg<LETTER, COLNAMES> naiOther = (NaiveDawg<LETTER, COLNAMES>) other;
		mBacking.removeAll(naiOther.mBacking);
	}
	
	private Set<List<LETTER>> getNCrossProduct() {
		if (mNCrossProduct == null) {
			mNCrossProduct = EprHelpers.computeNCrossproduct(mAllConstants, mArity);
		}
		return mNCrossProduct;
	}

	@Override
	public boolean supSetEq(IDawg<ApplicationTerm, TermVariable> other) {
		assert mColNames.equals(other.getColnames());
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void addAllWithSubsetSignature(IDawg<LETTER, COLNAMES> other) {
		assert mColNames.containsAll(other.getColnames());
		NaiveDawg<LETTER, COLNAMES> nd = (NaiveDawg<LETTER, COLNAMES>) other;
		//TODO: could be done nicer --> only go through the points that actually occur in this.mBacking..
		for (List<LETTER> pt : nd.mBacking) {
			mBacking.addAll(blowUpForCurrentSignature(pt, nd.mColNames));
		}
		
	}

	@Override
	public void removeAllWithSubsetSignature(IDawg<LETTER, COLNAMES> other) {
		assert mColNames.containsAll(other.getColnames());
		NaiveDawg<LETTER, COLNAMES> nd = (NaiveDawg<LETTER, COLNAMES>) other;
		//TODO: could be done nicer --> only go through the points that actually occur in this.mBacking..
		for (List<LETTER> pt : nd.mBacking) {
			mBacking.removeAll(blowUpForCurrentSignature(pt, nd.mColNames));
		}
	}

	private List<List<LETTER>> blowUpForCurrentSignature(List<LETTER> pt, SortedSet<COLNAMES> ptSig) {
		assert mColNames.containsAll(ptSig);
		List<List<LETTER>> result = new ArrayList<List<LETTER>>();
		for (COLNAMES cn : mColNames) {
			//TODO hacky
			int posInPtSig = -1;
			Iterator<COLNAMES> ptSigIt = ptSig.iterator();
			for (int i = 0; i < ptSig.size(); i++) {
//				if (ptSig.get(i) == cn) {
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
					for (LETTER c : mAllConstants) {
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
		return new NaiveDawg<LETTER, COLNAMES>(mColNames, mAllConstants, newBacking);
	}

	@Override
	protected Iterable<List<LETTER>> listPoints() {
		return mBacking;
	}

}
