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
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.BinaryRelation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;

public class DawgFactory<LETTER, COLNAMES> {
	
	private final EprTheory mEprTheory;
	Set<LETTER> mAllConstants;
	private LogProxy mLogger;
	
	
	private final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;
	private final DawgStateFactory mDawgStateFactory;
	
	/**
	 * Use naive Dawg implementation ("normal" one otherwise)
	 */
	private boolean mUseNaiveDawgs = true;

	public DawgFactory(Set<LETTER> allConstants, EprTheory eprTheory) {
		mEprTheory = eprTheory;
		mAllConstants = allConstants;
		mLogger = eprTheory.getLogger();

		if (mUseNaiveDawgs) {
			mDawgStateFactory = null;
			mDawgLetterFactory = null;
		} else {
			mDawgLetterFactory = new DawgLetterFactory<LETTER, COLNAMES>(mAllConstants);
			mDawgStateFactory = new DawgStateFactory();
		}
	}

	public IDawg<LETTER, COLNAMES> createEmptyDawg(SortedSet<COLNAMES> termVariables) {
		assert termVariables != null;
		//TODO freeze the current allConstants set, here?? or can it just change transparently?? 
		
		if (mUseNaiveDawgs) {
			return new NaiveDawg<LETTER, COLNAMES>(termVariables, mAllConstants, mLogger);
		} else {
			return new Dawg<LETTER, COLNAMES>(termVariables, mAllConstants, mLogger, this);
		}
	}

	/**
	 * Creates and returns a Dawg that accepts all words in Sigma^n.
	 * (where n = termVariables.length)
	 *
	 * @param termVariables
	 * @return
	 */
	public IDawg<LETTER, COLNAMES> createFullDawg(SortedSet<COLNAMES> termVariables) {
		assert termVariables != null;
		if (mUseNaiveDawgs) {
			return new NaiveDawg<LETTER, COLNAMES>(termVariables, mAllConstants, mLogger).complement();
		} else {
			return new Dawg<LETTER, COLNAMES>(termVariables, mAllConstants,  true, 
					mLogger, this);
		}
	}

	public IDawg<LETTER, COLNAMES> createOnePointDawg(
			SortedSet<COLNAMES> sig, List<LETTER> point) {
		if (mUseNaiveDawgs) {
			NaiveDawg<LETTER, COLNAMES> dawg = 
					new NaiveDawg<LETTER, COLNAMES>(sig, mAllConstants, mLogger);
			dawg.add(point);
			return dawg;
		} else {
			return new Dawg<LETTER, COLNAMES>(sig, 
					mAllConstants, point, mLogger, this);
		}
	}

	public IDawg<LETTER, COLNAMES> copyDawg(IDawg<LETTER, COLNAMES> dawg) {
		if (mUseNaiveDawgs) {
			NaiveDawg<LETTER, COLNAMES> nd = (NaiveDawg<LETTER, COLNAMES>) dawg;
			return new NaiveDawg<LETTER, COLNAMES>(nd, mLogger);
		} else {
			return null;
		}
	}
	

	/**
	 * Used for translating from the signature of a DecideStackLiteral to the signature of an EprClause with respect to
	 * a clause literals signature.
	 * A DecideStackLiteral has one variable for each argument of the underlying predicate.
	 * 
	 * example: 
	 *  - some DSL says something like P(x_0 x_1 x_2 x_3)
	 *  - the overall clause signature may be (u v w x y z)
	 *  - the clause literals arguments may be (v a w v) (i.e. there may be constants, repetitions, and different orderings)
	 *  
	 *  the input dawg has the signature of the DSL
	 *  
	 *  then we want to change the columns of the input dawg such that they match the clause's signature
	 *  this entails
	 *  - renamings -- x_0 -> v, x_2 -> w
	 *  - if there are repetitions or constants, we have to select accordingly, in the example we only select points 
	 *   where x_0 = x_3 and x_1 = a
	 *   --> from this we would get a dawg that describes the points wrt the clause literal
	 *  - we have to blow up the signature for the whole clause, i.e., for every missing column to the target signature we 
	 *   insert a "X Sigma", i.e., we compute the cross product with the whole set of constants
	 *    
	 *    
	 * In short, and in the applications of the EprTheory, this translates a Dawg with the signature of an EprPredicate to a Dawg with the signature
	 * of a clause (according to the given translation mapping that is stored in each ClauseEprQuantifiedPredicate)
	 *  
	 * @param dawg the dawg that is to be transformed
	 * @param translation a mapping from the variables in the input Dawgs signature to other TermVariables and/or constants
	 * @param targetSignature the target signature we want to blow up for in the end
	 * @return
	 */
	public IDawg<LETTER, COLNAMES> translatePredSigToClauseSig(
			IDawg<LETTER, COLNAMES> dawg, 
			Map<COLNAMES, COLNAMES> translationCnToCn, 
			Map<COLNAMES, LETTER> translationCnToLtr, 
			SortedSet<COLNAMES> targetSignature) {
		
		return dawg.translatePredSigToClauseSig(translationCnToCn, translationCnToLtr, targetSignature);
	}



	/**
	 * From the input dawg and translation computes a dawg
	 *  - whose points are rearranged according to the new signature
	 *  - constants in the argList are filled in the corresponding places at every point
	 *  - we exploit that the order of arglist matches the sorting order of the newSignature 
	 *    (that is fix for the given eprPredicate)
	 *  EDIT:
	 *   Pragmatically spoken this translated a dawg in the signature of an epr clause into a dawg in the signature of 
	 *   a decide stack literal. For this it uses the information from one clause literal whose predicate matches the 
	 *   decide stack literal's predicate.
	 * @param other
	 * @param translation a map translating the colnames of the old dawg ("other") to the colnames of the new dawg
	 *                    may not have a preimage for every new colname in the new signature because there constants 
	 *                    from argList are filled in
	 *                     (could be computed from arglist, right?..)
	 * @param argList
	 * @param newSignature
	 * @return
	 */
	public IDawg<LETTER, COLNAMES> translateClauseSigToPredSig(
			IDawg<LETTER, COLNAMES> other, 
			Map<COLNAMES, COLNAMES> translation, 
			List<Object> argList, 
			SortedSet<COLNAMES> newSignature) {
		return other.translateClauseSigToPredSig(translation, argList, newSignature);
	}
	
	

	public LogProxy getLogger() {
		return mLogger;
	}

	/////////////////////////////////////////////////////////////
	///////////////// test code /////////////////////////////////
	/////////////////////////////////////////////////////////////
		/**
		 *  Some tests for the DawgFactory
		 * @param args
		 */
		public static void main(String[] args) {
			
			// setup 
			
			Set<Character> constants = new HashSet<Character>();
			constants.add('a');
			constants.add('b');
			constants.add('c');
			
			
			DawgFactory<Character, String> df = 
					new DawgFactory<Character, String>(constants, null);
			
			SortedSet<String> colNames1 = new TreeSet<String>();
			colNames1.add("one");
			colNames1.add("two");
	//		colNames1.add("three");
	//		colNames1.add("four");
	//		colNames1.add("five");
			
			SortedSet<String> colNames2 = new TreeSet<String>();
			colNames2.add("alpha");
			colNames2.add("beta");
			colNames2.add("gamma");
	//		colNames1.add("delta");
	
	
			IDawg<Character, String> d1 = df.createFullDawg(colNames1);
	
			System.out.println("d1: (one, two), Sigma^*");
			System.out.println(d1);
	
			IDawg<Character, String> d2 = df.createEmptyDawg(colNames2);
			List<Character> word1 = new ArrayList<Character>();
			word1.add('a');
			word1.add('a');
			word1.add('b');
			d2.add(word1);
			
			List<Character> word2 = new ArrayList<Character>();
			word2.add('a');
			word2.add('b');
			word2.add('b');
			d2.add(word2);
	
			System.out.println("d2: (alpha, beta, gamma), { aab, abb } ");
			System.out.println(d2);
			
			// tests for renameSelectAndProject
			
//			Map<String, Object> translation3 = new HashMap<String, Object>();
//			translation3.put("alpha", "bla");
//			translation3.put("beta", "bla");
//			translation3.put("gamma", "blub");
//	
//			IDawg<Character, String> d3 = df.translatePredSigToClauseSig(d2, translation3, d2.getColnames());
//	
//			System.out.println("d3: rnsP(d2, {alpha -> bla, beta -> bla, gamma -> blub)");
//			System.out.println("expecting: (bla, blub) {ab}");
//			System.out.println(d3);
//			
//			Map<String, Object> translation4 = new HashMap<String, Object>();
//			translation4.put("alpha", "bla");
//			translation4.put("beta", "bla");
//			translation4.put("gamma", 'a');
//	
//			IDawg<Character, String> d4 = df.translatePredSigToClauseSig(d2, translation4, d2.getColnames());
//	
//			System.out.println("d4: rnsP(d2, {alpha -> bla, beta -> bla, gamma -> 'a')");
//			System.out.println("expecting: (bla) {}");
//			System.out.println(d4);
//	
//			Map<String, Object> translation5 = new HashMap<String, Object>();
//			translation5.put("alpha", "bla");
//			translation5.put("beta", "bla");
//			translation5.put("gamma", 'b');
//	
//			IDawg<Character, String> d5 = df.translatePredSigToClauseSig(d2, translation5, d2.getColnames());
	
//			System.out.println("d5: rnsP(d2, {alpha -> bla, beta -> bla, gamma -> 'b')");
//			System.out.println("expecting: (bla) {a}");
//			System.out.println(d5);
	
			// tests for renameAndRestoreConstants
			
//			BinaryRelation<String, String> translation6 = new BinaryRelation<String, String>();
//			translation6.addPair("alpha", "cinque");
//			translation6.addPair("beta", "uno");
//			translation6.addPair("gamma", "quattro");
	
			Map<String, String> translation6 = new HashMap<String, String>();
			translation6.put("cique", "alpha");
			translation6.put("uno", "beta");
			translation6.put("quattro", "gamma");
			
			List<Object> argList1 = new ArrayList<Object>();
			argList1.add("beta");
			argList1.add('B');
			argList1.add("gamma");
			argList1.add('A');
			argList1.add("alpha");
			
			SortedSet<String> newSignature1 = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
			newSignature1.add("uno");
			newSignature1.add("due");
			newSignature1.add("tre");
			newSignature1.add("quattro");
			newSignature1.add("cinque");

			
			IDawg<Character, String> d6 = df.translateClauseSigToPredSig(d2, translation6, argList1, newSignature1);

			System.out.println("d6: rnRc(d2, {alpha -> uno, beta -> due, gamma -> tre), "
					+ "(beta, B, gamma, A, alpha)" +  newSignature1);
			System.out.println("expecting: (due, cinque, quattro, tre, uno) {aBbAa, aBbAb}");
			System.out.println(d6);
		
		}

		public DawgLetterFactory<LETTER, COLNAMES> getDawgLetterFactory() {
			return mDawgLetterFactory;
		}

		public DawgStateFactory<LETTER, COLNAMES> getDawgStateFactory() {
			return mDawgStateFactory;
		}
	
}
