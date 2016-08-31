package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

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
	
	public NaiveDawg(COLNAMES[] termVariables, Set<LETTER> allConstants) {
		super(termVariables, allConstants);
		mBacking = new HashSet<List<LETTER>>();
	}

	public NaiveDawg(COLNAMES[] termVariables, Set<LETTER> allConstants, 
			Set<List<LETTER>> initialLanguage) {
		super(termVariables, allConstants);
		mBacking = new HashSet<List<LETTER>>(initialLanguage);
	}


	public NaiveDawg(NaiveDawg<LETTER, COLNAMES> nd) {
		super(nd.mColNames, nd.mAllConstants);
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

}
