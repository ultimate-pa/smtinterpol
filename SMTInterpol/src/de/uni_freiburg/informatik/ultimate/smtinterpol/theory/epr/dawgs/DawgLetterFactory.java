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

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class DawgLetterFactory<LETTER, COLNAMES> {
	
	
	UniversalDawgLetter<LETTER, COLNAMES> mUniversalDawgLetter;
	EmptyDawgLetter<LETTER, COLNAMES> mEmptyDawgLetter;

	EmptyDawgLetterWithEqualities<LETTER, COLNAMES> mEmptyDawgLetterWithEqualities
	 	= new EmptyDawgLetterWithEqualities<LETTER, COLNAMES>(this);
	UniversalDawgLetterWithEqualities<LETTER, COLNAMES> mUniversalDawgLetterWithEqualities
	 	= new UniversalDawgLetterWithEqualities<LETTER, COLNAMES>(this);

	Set<IDawgLetter<LETTER, COLNAMES>> mUniversalDawgLetterSingleton;
	Set<IDawgLetter<LETTER, COLNAMES>> mEmptyDawgLetterSingleton;
	
	Map<Set<LETTER>, SimpleDawgLetter<LETTER, COLNAMES>> mLettersToSimpleDawgLetter
		 = new HashMap<Set<LETTER>, SimpleDawgLetter<LETTER,COLNAMES>>();
	private Map<Set<LETTER>, SimpleComplementDawgLetter<LETTER, COLNAMES>> mLettersToSimpleComplementDawgLetter
		 = new HashMap<Set<LETTER>, SimpleComplementDawgLetter<LETTER,COLNAMES>>();
	
	NestedMap3<Set<LETTER>, Set<COLNAMES>, Set<COLNAMES>, DawgLetterWithEqualities<LETTER, COLNAMES>> mKnownDawgLetters;

	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	

	public DawgLetterFactory(DawgFactory<LETTER, COLNAMES> dawgFactory) {
		mDawgFactory = dawgFactory;
		
		mKnownDawgLetters = 
				new NestedMap3<Set<LETTER>, Set<COLNAMES>, Set<COLNAMES>, DawgLetterWithEqualities<LETTER,COLNAMES>>();

		mUniversalDawgLetter = new UniversalDawgLetter<LETTER, COLNAMES>(this);
		mEmptyDawgLetter = new EmptyDawgLetter<LETTER, COLNAMES>(this);
		mEmptyDawgLetterSingleton = Collections.singleton((IDawgLetter<LETTER, COLNAMES>) mEmptyDawgLetter);
		mUniversalDawgLetterSingleton = Collections.singleton((IDawgLetter<LETTER, COLNAMES>) mUniversalDawgLetter);
	}

	public IDawgLetter<LETTER, COLNAMES> getSingletonSetDawgLetter(LETTER element) {
		if (useSimpleDawgLetters()) {
			return getSimpleDawgLetter(Collections.singleton(element));
		} else {
			Set<COLNAMES> es = Collections.emptySet();
			return getDawgLetter(Collections.singleton(element), es, es);
		}
	}
	
	public IDawgLetter<LETTER, COLNAMES> getUniversalDawgLetter() {
		if (useSimpleDawgLetters()) {
			return mUniversalDawgLetter;
		} else {
			return mUniversalDawgLetterWithEqualities;
		}
	}
	
	public IDawgLetter<LETTER, COLNAMES> getEmptyDawgLetter() {
		if (useSimpleDawgLetters()) {
			return mEmptyDawgLetter;
		} else {
			return mEmptyDawgLetterWithEqualities;
		}
	}

	public DawgLetterWithEqualities<LETTER, COLNAMES> getDawgLetter(Set<LETTER> newLetters, Set<COLNAMES> equalColnames,
			Set<COLNAMES> inequalColnames) {

		if (newLetters.isEmpty()) {
			// if the set of LETTERs is empty, the (in)equalities don't matter
			return mEmptyDawgLetterWithEqualities;
		}
		
//		if (newLetters.equals(mAllConstants) 
//				&& equalColnames.isEmpty() 
//				&& inequalColnames.isEmpty()) {
//			return mUniversalDawgLetterWithEqualities;
//		}
		
		DawgLetterWithEqualities<LETTER, COLNAMES> result = mKnownDawgLetters.get(newLetters, equalColnames, inequalColnames);
		if (result == null) {
			result = new DawgLetterWithEqualities<LETTER, COLNAMES>(newLetters, equalColnames, inequalColnames, this);
			mKnownDawgLetters.put(newLetters, equalColnames, inequalColnames, result);
		}
		
		return result;
	}
	
	public Set<LETTER> getAllConstants() {
		return mDawgFactory.getAllConstants();
	}
	


	/**
	 * Takes a set of DawgLetters and returns a set of DawgLetters that represents the complement
	 * of the LETTERs represented by the input set.
	 * 
	 * Conceptually a set of DawgLetters is a kind of DNF (a DawgLetter is a cube with one set-constraint
	 * and some equality and inequality constraints).
	 * This method has to negate the DNF and bring the result into DNF again.
	 * 
	 * @param outgoingDawgLetters
	 * @return
	 */
	public Set<IDawgLetter<LETTER, COLNAMES>> complementDawgLetterSet(
			Set<IDawgLetter<LETTER, COLNAMES>> dawgLetters) {
		if (useSimpleDawgLetters()) {
			if (dawgLetters.isEmpty()) {
				return Collections.singleton(getUniversalDawgLetter());
			}
			
			if (dawgLetters.iterator().next() instanceof UniversalDawgLetter<?, ?>) {
				assert dawgLetters.size() == 1 : "should normalize this, right?..";
				return Collections.emptySet();
			}
			
			IDawgLetter<LETTER, COLNAMES> resultDl = getUniversalDawgLetter();
			for (IDawgLetter<LETTER, COLNAMES> dl : dawgLetters) {
				final Set<IDawgLetter<LETTER, COLNAMES>> dlComplement = dl.complement();
				assert dlComplement.size() == 1 : "should hold in the simpleDawgLetter case, right?";
				resultDl = resultDl.intersect(dlComplement.iterator().next());
			}
//			
//			final Set<LETTER> resultLetters = new HashSet<LETTER>();
//			resultLetters.addAll(getAllConstants());
//			for (IDawgLetter<LETTER, COLNAMES> dl : dawgLetters) {
//				if (dl instanceof SimpleDawgLetter<?, ?>) {
//					resultLetters.removeAll(((SimpleDawgLetter<LETTER, COLNAMES>) dl).getLetters());
//					
//				} else if (dl instanceof SimpleComplementDawgLetter<?, ?>) {
//
//				} else {
//					assert false : "treat this case?";
//				}
//			}
//
//			IDawgLetter<LETTER, COLNAMES> resultDl = getSimpleDawgLetter(resultLetters);
			if (resultDl instanceof EmptyDawgLetter<?, ?>) {
				return Collections.emptySet();
			}
			return Collections.singleton(resultDl);
		} else {
			// TODO: wouldn't it be simple to use the intersect and complement operations, like above??

			Set<IDawgLetter<LETTER, COLNAMES>> result = new HashSet<IDawgLetter<LETTER,COLNAMES>>();
			result.add(mUniversalDawgLetterWithEqualities);

			for (IDawgLetter<LETTER, COLNAMES> dln: dawgLetters) {
				DawgLetterWithEqualities<LETTER, COLNAMES> dl = (DawgLetterWithEqualities<LETTER, COLNAMES>) dln;

				Set<IDawgLetter<LETTER, COLNAMES>> newResult = new HashSet<IDawgLetter<LETTER,COLNAMES>>();

				for (IDawgLetter<LETTER, COLNAMES> dlResN : result) {
					DawgLetterWithEqualities<LETTER, COLNAMES> dlRes = (DawgLetterWithEqualities<LETTER, COLNAMES>) dlResN;

					{
						HashSet<LETTER> newLetters = new HashSet<LETTER>(dlRes.getLetters());
						newLetters.retainAll(dl.getLetters());
						if (!newLetters.isEmpty()) {
							DawgLetterWithEqualities<LETTER, COLNAMES> newDl1 = 
									new DawgLetterWithEqualities<LETTER, COLNAMES>(
											newLetters, 
											dlRes.getEqualColnames(), 
											dlRes.getUnequalColnames(), 
											this);
							newResult.add(newDl1);
						}
					}

					for (COLNAMES eq : dlRes.getEqualColnames()) {
						if (dlRes.getUnequalColnames().contains(eq)) {
							// DawgLetter would be empty
							continue;
						}
						Set<COLNAMES> newEquals = new HashSet<COLNAMES>(dlRes.getEqualColnames());
						newEquals.add(eq);
						DawgLetterWithEqualities<LETTER, COLNAMES> newDl2 = 
								new DawgLetterWithEqualities<LETTER, COLNAMES>(
										dlRes.getLetters(), 
										newEquals, 
										dlRes.getUnequalColnames(), 
										this);
						newResult.add(newDl2);
					}

					for (COLNAMES unEq : dlRes.getUnequalColnames()) {
						if (dlRes.getEqualColnames().contains(unEq)) {
							// DawgLetter would be empty
							continue;
						}
						Set<COLNAMES> newUnequals = new HashSet<COLNAMES>(dlRes.getUnequalColnames());
						newUnequals.add(unEq);
						DawgLetterWithEqualities<LETTER, COLNAMES> newDl3 = 
								new DawgLetterWithEqualities<LETTER, COLNAMES>(
										dlRes.getLetters(), 
										dlRes.getEqualColnames(), 
										newUnequals, 
										this);
						newResult.add(newDl3);
					}

				}
				result = newResult;
			}

			return result;
		}
	}

	/**
	 * 
	 * @param letters an implicitly disjunctive set of DawgLetters
	 * @return
	 */
	public static <LETTER, COLNAMES> boolean isUniversal(Set<IDawgLetter<LETTER, COLNAMES>> letters) {
		if (letters.size() == 0) {
			return false;
		}
		if (letters.size() == 1 && letters.iterator().next() instanceof EmptyDawgLetter<?, ?>) {
			return false;
		}
		if (letters.size() == 1 && letters.iterator().next() instanceof UniversalDawgLetter<?, ?>) {
			return true;
		}
		if (letters.size() >= 1 && letters.iterator().next() instanceof SimpleDawgLetter<?, ?>) {
			/**
			 * the DawgLetters are universal (as a disjunction) if and only if the SimpleDawgLetters
			 * and the SimpleComplementDawgLetters complement each other perfectly.
			 */
			Set<LETTER> unionNormal = new HashSet<LETTER>();
			Set<LETTER> unionComplement = new HashSet<LETTER>();
			for (IDawgLetter<LETTER, COLNAMES> outLetter : letters) {
				if (outLetter instanceof SimpleDawgLetter<?, ?>) {
					unionNormal.addAll(((SimpleDawgLetter<LETTER, COLNAMES>) outLetter).getLetters());
				} else if (outLetter instanceof SimpleComplementDawgLetter<?, ?>) {
					unionComplement.addAll(
							((SimpleComplementDawgLetter<LETTER, COLNAMES>) outLetter).getComplementLetters());
				} else if (outLetter instanceof UniversalDawgLetter) {
					assert false : "a universal dawg letter and another one?";
				} else if (outLetter instanceof EmptyDawgLetter<?, ?>) {
					// do nothing
				} else {
					assert false : "unexpected mixing of DawgLetter types";
				}
			}
			return unionNormal.equals(unionComplement);
		}
		assert false : "TODO";
		return false;
	}

	public IDawgLetter<LETTER, COLNAMES> getSimpleDawgLetter(Set<LETTER> letters) {
		if (letters.isEmpty()) {
			 return getEmptyDawgLetter();
		}
		
		IDawgLetter<LETTER, COLNAMES> result = mLettersToSimpleDawgLetter.get(letters);
		if (result == null) {
			result = new SimpleDawgLetter<LETTER, COLNAMES>(this, letters);
			mLettersToSimpleDawgLetter.put(letters, (SimpleDawgLetter<LETTER, COLNAMES>) result);
		}
		return result;
	}
	
	public IDawgLetter<LETTER, COLNAMES> getSimpleComplementDawgLetter(Set<LETTER> letters) {
		if (letters.isEmpty()) {
			 return getUniversalDawgLetter();
		}
		
		IDawgLetter<LETTER, COLNAMES> result = mLettersToSimpleComplementDawgLetter.get(letters);
		if (result == null) {
			result = new SimpleComplementDawgLetter<LETTER, COLNAMES>(this, letters);
			mLettersToSimpleComplementDawgLetter.put(letters, (SimpleComplementDawgLetter<LETTER, COLNAMES>) result);
		}
		return result;
	}

	public boolean useSimpleDawgLetters() {
		return true;
	}
}
