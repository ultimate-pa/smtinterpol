package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
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
	
	public NaiveDawg(List<COLNAMES> termVariables, Set<LETTER> allConstants) {
		super(termVariables, allConstants);
		mBacking = new HashSet<List<LETTER>>();
	}

	public NaiveDawg(List<COLNAMES> termVariables, Set<LETTER> allConstants, 
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

	@Override
	public IDawgSubstitution join(IDawg<LETTER, COLNAMES> other) {
		// TODO Auto-generated method stub
		return null;
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
	public void add(LETTER[] arguments) {
		mBacking.add(Arrays.asList(arguments));
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
	 * TODO: set intersection or natural join??
	 */
	@Override
	public IDawg<LETTER, COLNAMES> intersect(IDawg<LETTER, COLNAMES> other) {
		NaiveDawg<LETTER, COLNAMES> naiOther = (NaiveDawg<LETTER, COLNAMES>) other;
		
		Set<List<LETTER>> newBacking = new HashSet<List<LETTER>>(mBacking);
		newBacking.retainAll(naiOther.mBacking);
		
		return new NaiveDawg<LETTER, COLNAMES>(mColNames, mAllConstants, newBacking);
	}

	@Override
	public void removeAll(IDawg<LETTER, COLNAMES> other) {
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
	public boolean supSetEq(IDawg<ApplicationTerm, TermVariable> points) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void addAllWithSubsetSignature(IDawg<LETTER, COLNAMES> d1) {
		NaiveDawg<LETTER, COLNAMES> nd1 = (NaiveDawg<LETTER, COLNAMES>) d1;
		for (List<LETTER> pt : nd1.mBacking) {
			mBacking.addAll(blowUpForCurrentSignature(pt, nd1.mColNames));
		}
		
	}

	private List<List<LETTER>> blowUpForCurrentSignature(List<LETTER> pt, List<COLNAMES> ptSig) {
		List<List<LETTER>> result = new ArrayList<List<LETTER>>();
		for (COLNAMES cn : mColNames) {
			//TODO hacky
			int posInPtSig = -1;
			for (int i = 0; i < ptSig.size(); i++) {
				if (ptSig.get(i) == cn) {
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

}
