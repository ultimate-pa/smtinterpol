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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.BinaryRelation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

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
	private final ScopedHashMap<Object, Set<LETTER>> mAllConstants;
	
	public NaiveDawg(SortedSet<COLNAMES> termVariables, ScopedHashMap<Object, Set<LETTER>> allConstants, LogProxy logger) {
		super(termVariables, logger);
		mAllConstants = allConstants;
		mBacking = new HashSet<List<LETTER>>();
	}

	public NaiveDawg(SortedSet<COLNAMES> termVariables, ScopedHashMap<Object, Set<LETTER>> allConstants, 
			Set<List<LETTER>> initialLanguage, LogProxy logger) {
		super(termVariables, logger);
		mAllConstants = allConstants;
		mBacking = new HashSet<List<LETTER>>(initialLanguage);
	}


	public NaiveDawg(NaiveDawg<LETTER, COLNAMES> nd, LogProxy logger) {
		super(nd.getColNames(), logger);
		mAllConstants = nd.mAllConstants;
		mBacking = new HashSet<List<LETTER>>(nd.mBacking);
	}

	public NaiveDawg(NaiveDawg<LETTER, COLNAMES> nd, Map<COLNAMES, COLNAMES> translation, LogProxy logger) {
		super(EprHelpers.applyMapping(nd.getColNames(), translation), logger);
		mAllConstants = nd.mAllConstants;
		mBacking = new HashSet<List<LETTER>>(nd.mBacking);
	}

//	@Override
//	public IDawg<LETTER, COLNAMES> join(IDawg<LETTER, COLNAMES> other) {
//		// union signature
//		SortedSet<COLNAMES> newSignature = new TreeSet<COLNAMES>(EprHelpers.getColumnNamesComparator());
//		newSignature.addAll(this.mColNames);
//		newSignature.addAll(other.getColnames());
//
//		// intersection signature
//		SortedSet<COLNAMES> commonColumns = new TreeSet<COLNAMES>(newSignature);
//		commonColumns.retainAll(this.mColNames);
//		commonColumns.retainAll(other.getColnames());
//
//		NaiveDawg<LETTER, COLNAMES> otherNd = (NaiveDawg<LETTER, COLNAMES>) other;
//
//		NaiveDawg<LETTER, COLNAMES> result = 
//				new NaiveDawg<LETTER, COLNAMES>(newSignature, mAllConstants, mLogger);
//		
//		for (List<LETTER> pointThis : this.mBacking) {
//			for (List<LETTER> pointOther : otherNd.mBacking) {
//				List<LETTER> joinedPoint = new ArrayList<LETTER>(newSignature.size());
//				for (COLNAMES cn : newSignature) {
//					Integer thisColIndex = this.mColNameToIndex.get(cn);
//					Integer otherColIndex = otherNd.mColNameToIndex.get(cn);
//					if (thisColIndex != null 
//							&& otherColIndex != null 
//							&& pointThis.get(thisColIndex) != pointOther.get(otherColIndex)) {
//						// cn is a common column and
//						// the two points don't match on it
//						joinedPoint = null;
//						break;
//					}
//					LETTER lThis = thisColIndex != null ? pointThis.get(thisColIndex) : null;
//					LETTER lOther = otherColIndex != null ? pointOther.get(otherColIndex) : null;
//					assert lThis == null || lOther == null || lThis == lOther;
//					joinedPoint.add(lThis != null ? lThis : lOther);
//				}
//				// if we reach here, the two points do match on all common columns
//				if (joinedPoint != null) {
//					result.add(joinedPoint);
//				}
//			}
//		}
//		return result;
//	}

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
		assert EprHelpers.verifySortsOfPoints(complement, getColNames());
		complement.removeAll(mBacking);
		NaiveDawg<LETTER, COLNAMES> result = new NaiveDawg<LETTER, COLNAMES>(getColNames(), mAllConstants, complement, mLogger);
		assert EprHelpers.verifySortsOfPoints(result, getColNames());
		return result;
	}

//	@Override
//	public IDawg<LETTER, COLNAMES> union(IDawg<LETTER, COLNAMES> other) {
//		assert other.getColnames().equals(getColnames()) : "incompatible column names";
//
//		NaiveDawg<LETTER, COLNAMES> newDawg = 
//				new NaiveDawg<LETTER, COLNAMES>(mColNames, mAllConstants, mBacking, mLogger);
//		newDawg.addAll(other);
//
//		return newDawg;
//	}

	@Override
	public boolean accepts(List<LETTER> word) {
		assert mSignature.size() == word.size();
		return mBacking.contains(word);
	}

	@Override
	public IDawg<LETTER, COLNAMES> add(List<LETTER> point) {
		assert EprHelpers.verifySortsOfPoint(point, this.getColNames());
		mBacking.add(point);
		return this;
	}

//	@Override
//	public void addAll(IDawg<LETTER, COLNAMES> other) {
//		super.addAll(other);
//		// assuming that we use NaiveDawgs for all Dawgs..
//		NaiveDawg<LETTER, COLNAMES> naiOther = (NaiveDawg<LETTER, COLNAMES>) other;
//		assert EprHelpers.verifySortsOfPoints(naiOther, getColnames());
//		mBacking.addAll(naiOther.mBacking);
//	}

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
		assert getColNames().equals(other.getColNames());
		NaiveDawg<LETTER, COLNAMES> naiOther = (NaiveDawg<LETTER, COLNAMES>) other;
		
		Set<List<LETTER>> newBacking = new HashSet<List<LETTER>>(mBacking);
		newBacking.retainAll(naiOther.mBacking);
		
		return new NaiveDawg<LETTER, COLNAMES>(getColNames(), mAllConstants, newBacking, mLogger);
	}

//	@Override
//	public void removeAll(IDawg<LETTER, COLNAMES> other) {
//		assert mColNames.equals(other.getColnames());
//		NaiveDawg<LETTER, COLNAMES> naiOther = (NaiveDawg<LETTER, COLNAMES>) other;
//		mBacking.removeAll(naiOther.mBacking);
//	}
	
	private Set<List<LETTER>> getNCrossProduct() {
		if (mNCrossProduct == null) {
			assert false : "TODO: restore below functionality";
//			mNCrossProduct = EprHelpers.computeNCrossproduct(mAllConstants, mArity, mLogger);
		}
		return mNCrossProduct;
	}

	@Override
	public boolean supSetEq(IDawg<LETTER, COLNAMES> other) {
		assert getColNames().equals(other.getColNames());
		NaiveDawg<LETTER, COLNAMES> otherNd = (NaiveDawg<LETTER, COLNAMES>) other;
		return this.mBacking.containsAll(otherNd.mBacking);
	}

//	@Override
//	public void addAllWithSubsetSignature(IDawg<LETTER, COLNAMES> other) {
//		assert mColNames.containsAll(other.getColnames());
//		NaiveDawg<LETTER, COLNAMES> nd = (NaiveDawg<LETTER, COLNAMES>) other;
//		//TODO: could be done nicer --> only go through the points that actually occur in this.mBacking..
//		for (List<LETTER> pt : nd.mBacking) {
//			addWithSubsetSignature(pt, nd.mColNames);
//		}
//	}

//	@Override
//	public void removeAllWithSubsetSignature(IDawg<LETTER, COLNAMES> other) {
//		assert mColNames.containsAll(other.getColnames());
//		NaiveDawg<LETTER, COLNAMES> nd = (NaiveDawg<LETTER, COLNAMES>) other;
//		//TODO: could be done nicer --> only go through the points that actually occur in this.mBacking..
//		for (List<LETTER> pt : nd.mBacking) {
//			mBacking.removeAll(blowUpForCurrentSignature(pt, nd.mColNames, mColNames, mAllConstants));
//		}
//	}

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
		assert getColNames().containsAll(selectMap.keySet());
		Set<List<LETTER>> newBacking = new HashSet<List<LETTER>>(mBacking);
		for (List<LETTER> word : mBacking) {
			for (Entry<COLNAMES, LETTER> en : selectMap.entrySet()) {
				int index = getColNameToIndex().get(en.getKey());
				if (word.get(index) != en.getValue()) {
					newBacking.remove(word);
				}
			}
		}
		return new NaiveDawg<LETTER, COLNAMES>(getColNames(), mAllConstants, newBacking, mLogger);
	}

	@Override
	public Iterable<List<LETTER>> getAllPointsSorted() {
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
		assert false : "TODO: restore below functionality";
//		mBacking.addAll(blowUpForCurrentSignature(point, sig, mColNames, mAllConstants));
	}
	
	
	@Override
	public IDawg<LETTER, COLNAMES> translatePredSigToClauseSig(
			Map<COLNAMES, COLNAMES> translationColnameToColname,
			Map<COLNAMES, LETTER> translationColnameToLetter,
			DawgSignature<COLNAMES> targetSignature) {

//		COLNAMES colNamesInstance = this.getColnames().first();
		
		// the signature of the new dawg has only the non-duplicated colnames 
		// and also omits constants (i.e. objects not of the type COLNAMES)
		// this signature is before the blowup to targetSignature
		SortedSet<COLNAMES> newPointSignature = new TreeSet<COLNAMES>(EprHelpers.getColumnNamesComparator());
		newPointSignature.addAll(translationColnameToColname.values());
//		for (Object o : translation.values()) {
//			if (colNamesInstance.getClass().isInstance(o)) {
//				newPointSignature.add((COLNAMES) o);
//			}
//		}
		
		// the new signature is repetition-free, so we can use a map
		Map<COLNAMES, Integer> newSigColNamesToIndex = EprHelpers.computeColnamesToIndex(newPointSignature);
		
		NaiveDawg<LETTER, COLNAMES> otherNd = this;
//		Set<List<LETTER>> newBacking = new HashSet<List<LETTER>>();
		NaiveDawg<LETTER, COLNAMES> result = new NaiveDawg<LETTER, COLNAMES>(targetSignature.getColNames(), mAllConstants, mLogger);

		for (List<LETTER> point : otherNd.mBacking) {

			List<LETTER> newPoint = new ArrayList<LETTER>(newPointSignature.size());
			// set up the new point (need to fill it, or List.set(..) won't work)
			for (int i = 0; i < newPointSignature.size(); i++) {
				newPoint.add(null);
			}
			
			// tracks if a column name has been seen, and what letter it had been assigned (does select_x=x so to say)
			Map<COLNAMES, LETTER> variableAssignmentInPoint = new HashMap<COLNAMES, LETTER>();
			
			Iterator<COLNAMES> ptColIt = this.getColNames().iterator();
			for (int i = 0; i < point.size(); i++) {
				LETTER ptLtr = point.get(i);
				COLNAMES ptColnameInOldSig = ptColIt.next();

//				Object translatedColumnName = translation.get(ptColnameInOldSig);
//				if (colNamesInstance.getClass().isInstance(translatedColumnName)) {
				COLNAMES colnameTranslation = translationColnameToColname.get(ptColnameInOldSig);
				LETTER letterTranslation = translationColnameToLetter.get(ptColnameInOldSig);
				if (colnameTranslation != null) {
					COLNAMES ptColnameInNewSig = colnameTranslation;
					
					LETTER vaip = variableAssignmentInPoint.get(ptColnameInNewSig);
					if (vaip != null && vaip != ptLtr) {
						// violation of select_x=x
						newPoint = null;
						break;
					} else {
						newPoint.set(newSigColNamesToIndex.get(ptColnameInNewSig), ptLtr);
						// store that at the current oldColumn-name we used letter ptLtr
						variableAssignmentInPoint.put(ptColnameInNewSig, ptLtr);
					}
					
				} else if (letterTranslation != null) {
					// we have a constant in the column where this letter in the point is supposed to "land"
					// select_x=c so to say..
					if (ptLtr.equals(letterTranslation)) {
						// the constant matches go on (add nothing to the new point)
					} else {
						// point is filtered by the select that checks the constants
						newPoint = null;
						break;
					}
				} else {
					assert false : "should not happen";
				}
			}
			if (newPoint != null) {
				result.addWithSubsetSignature(newPoint, newPointSignature);
//				newBacking.add(newPoint);
			}
		}
		assert EprHelpers.verifySortsOfPoints(result, targetSignature.getColNames());
		return result;
	}
	
	@Override
	@SuppressWarnings("unchecked")
	public IDawg<LETTER, COLNAMES> translateClauseSigToPredSig(
			BinaryRelation<COLNAMES, COLNAMES> translation, 
			List<Object> argList, 
			DawgSignature<COLNAMES> newSignature) {
		
		assert argList.size() == newSignature.size();
		
		Class<? extends Object> colnamesType = newSignature.getColNames().iterator().next().getClass();

		// the signature of a dawg of a decide stack literal does not contain repetitions, right?
		Map<COLNAMES, Integer> oldSigColnamesToIndex = EprHelpers.computeColnamesToIndex(this.getColNames());

		Set<List<LETTER>> newBacking = new HashSet<List<LETTER>>();
		NaiveDawg<LETTER, COLNAMES> otherNd = (NaiveDawg<LETTER, COLNAMES>) this;
		
		for (List<LETTER> point : otherNd.mBacking) {
			List<LETTER> newPoint = new ArrayList<LETTER>(newSignature.size());
			// add placeholders so we can later use List.set(..)
			for (int i = 0; i < newSignature.size(); i++) {
				newPoint.add(null);
			}

			Iterator<COLNAMES> newSigColIt = newSignature.getColNames().iterator();
			for (int i = 0; i < newSignature.size(); i++) {
				COLNAMES newSigColname = newSigColIt.next();
				if (!colnamesType.isInstance(argList.get(i))) {
					//argList.get(i) is a constant (because it is not a colname/termVariable)
					assert newPoint.get(i) == null :
						"the translation map must not translate to a colname where the clauseliteral has a constant!";
					newPoint.set(i, (LETTER) argList.get(i));
				} else {
					Set<COLNAMES> oldSigColnames = translation.getPreImage(newSigColname);
					assert oldSigColnames.size() == 1;
					final COLNAMES oldSigColname = oldSigColnames.iterator().next();
					LETTER letter = point.get(oldSigColnamesToIndex.get(oldSigColname));
					newPoint.set(i, letter);
				}
			}
			
			
			newBacking.add(newPoint);
		}
		
		NaiveDawg<LETTER, COLNAMES> result = 
				new NaiveDawg<LETTER, COLNAMES>(newSignature.getColNames(), mAllConstants, newBacking, mLogger);
		assert EprHelpers.verifySortsOfPoints(result, newSignature.getColNames());
		return result;
	}

	@Override
	public IDawg<LETTER, COLNAMES> union(IDawg<LETTER, COLNAMES> other) {
		HashSet<List<LETTER>> newBacking = new HashSet<List<LETTER>>(mBacking);
		newBacking.addAll(((NaiveDawg<LETTER, COLNAMES>)other).mBacking);
		return new NaiveDawg<LETTER, COLNAMES>(getColNames(), mAllConstants, newBacking, mLogger);
	}

	@Override
	public IDawg<LETTER, COLNAMES> difference(IDawg<LETTER, COLNAMES> other) {
		assert getColNames().equals(other.getColNames());
		NaiveDawg<LETTER, COLNAMES> naiOther = (NaiveDawg<LETTER, COLNAMES>) other;
		Set<List<LETTER>> newBacking = new HashSet<List<LETTER>>(mBacking);
		newBacking.removeAll(naiOther.mBacking);
		return new NaiveDawg<LETTER, COLNAMES>(
				getColNames(), mAllConstants, newBacking, mLogger);
	}

	@Override
	public Dawg<LETTER, COLNAMES> projectColumnAway(COLNAMES column) {
		assert false : "do we need an implementation in the NaivedDawg-case??";
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Dawg<LETTER, COLNAMES> computeSymmetricTransitiveClosure() {
		// TODO Auto-generated method stub
		return null;
	}

}
