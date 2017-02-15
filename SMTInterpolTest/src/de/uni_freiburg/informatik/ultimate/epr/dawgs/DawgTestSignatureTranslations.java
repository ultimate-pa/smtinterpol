/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.epr.dawgs;

import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.BinaryRelation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.Dawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.ReorderAndRenameDawgBuilder;

@RunWith(JUnit4.class)
public class DawgTestSignatureTranslations {

	private IDawg<String, Integer> dawg1;
	private List<String> word_aa;
	private List<String> word_ab;
	private List<String> word_ac;
	private List<String> word_ba;
	private List<String> word_bb;
	private List<String> word_bc;
	private List<String> word_ca;
	private List<String> word_cb;
	private List<String> word_cc;
	private IDawg<String, String> dawg3;

	Set<String> getAllConstants() {
		Set<String> result = new HashSet<String>();
		result.add("a");
		result.add("b");
		result.add("c");
		return result;
	}

	private EprTheory getEprTheory() {
		return new EprTheoryMock(getLogger());
	}
	
	private LogProxy getLogger() {
		return new DefaultLogger();
	}

	@Test
	public void test1() {
		
		DawgFactory<String, Integer> dawgFactoryStringInteger = 
				new DawgFactory<String, Integer>(getEprTheory(), getAllConstants());
		
		
		word_aa = Arrays.asList(new String[] { "a", "a" });
		word_ab = Arrays.asList(new String[] { "a", "b" });
		word_ac = Arrays.asList(new String[] { "a", "c" });
		word_ba = Arrays.asList(new String[] { "b", "a" });
		word_bb = Arrays.asList(new String[] { "b", "b" });
		word_bc = Arrays.asList(new String[] { "b", "c" });
		word_ca = Arrays.asList(new String[] { "c", "a" });
		word_cb = Arrays.asList(new String[] { "c", "b" });
		word_cc = Arrays.asList(new String[] { "c", "c" });


		SortedSet<Integer> signature1 = new TreeSet<Integer>(EprHelpers.getColumnNamesComparator());
		signature1.addAll(Arrays.asList(new Integer[] { 1, 2 }));
		
		dawg1 = dawgFactoryStringInteger.getEmptyDawg(signature1);
		dawg1 = dawg1.add(word_ba);
		dawg1 = dawg1.add(word_ca);

		assertTrue(dawg1.accepts(word_ba));
		assertTrue(dawg1.accepts(word_ca));
				
		SortedSet<Integer> signature2 = new TreeSet<Integer>(EprHelpers.getColumnNamesComparator());
		signature2.addAll(Arrays.asList(new Integer[] { 10, 20, 30 }));

		BinaryRelation<Integer, Integer> translation1 = new BinaryRelation<Integer, Integer>();
		translation1.addPair(1, 20);
		translation1.addPair(1, 30);
		translation1.addPair(2, 10);

		List<Object> argList1 = Arrays.asList(new Object[] { 1, 1, 2 });
		

		IDawg<String, Integer> dawg2 = dawg1.translateClauseSigToPredSig(translation1, argList1, signature2);
				
		
		assertTrue(dawg2.accepts(Arrays.asList(new String[] { "a", "b", "b" })));
		assertTrue(dawg2.accepts(Arrays.asList(new String[] { "a", "c", "c" })));
		
	}
	
	/**
	 * Example for RenameAndReorder which
	 *  - moves from left to right
	 *  - source column is not at the very start
	 *  - target column is not at the very end
	 * 
	 *  (example from the whiteboard in Jan/Feb 2017)
	 */
	@Test
	public void test2() {
		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory(), getAllConstants());

		/*
		 * words in the original automaton
		 */
		List<String> word_aaaaa = Arrays.asList(new String[] { "a", "a", "a", "a", "a" });
		List<String> word_aaacb = Arrays.asList(new String[] { "a", "a", "a", "c", "b" });
		List<String> word_aacbb = Arrays.asList(new String[] { "a", "a", "c", "b", "b" });
		List<String> word_aaccc = Arrays.asList(new String[] { "a", "a", "c", "c", "c" });
		List<String> word_acbaa = Arrays.asList(new String[] { "a", "c", "b", "a", "a" });
		List<String> word_acbcb = Arrays.asList(new String[] { "a", "c", "b", "c", "b" });
		List<String> word_babaa = Arrays.asList(new String[] { "b", "a", "b", "a", "a" });
		List<String> word_babcb = Arrays.asList(new String[] { "b", "a", "b", "c", "b" });
		List<String> word_aacab = Arrays.asList(new String[] { "a", "a", "c", "a", "b" });

		/*
		 * words that should be in the transformed automaton
		 */
		List<String> word_acbab = Arrays.asList(new String[] { "a", "c", "b", "a", "b" });
		List<String> word_accac = Arrays.asList(new String[] { "a", "c", "c", "a", "c" });
		List<String> word_abaca = Arrays.asList(new String[] { "a", "b", "a", "c", "a" });
		List<String> word_abccb = Arrays.asList(new String[] { "a", "b", "c", "c", "b" });
		List<String> word_bbaaa = Arrays.asList(new String[] { "b", "b", "a", "a", "a" });
		List<String> word_bbcab = Arrays.asList(new String[] { "b", "b", "c", "a", "b" });
		
		SortedSet<String> signature3 = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signature3.addAll(Arrays.asList(new String[] { "u", "v", "w", "x", "z"}));
		
		SortedSet<String> signature4 = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signature4.addAll(Arrays.asList(new String[] { "u", "w", "x", "y", "z" }));
		
		dawg3 = dawgFactoryStringString.getEmptyDawg(signature3);
		dawg3 = dawg3.add(word_aaaaa);
		dawg3 = dawg3.add(word_aaacb);
		dawg3 = dawg3.add(word_aacbb);
		dawg3 = dawg3.add(word_aaccc);
		dawg3 = dawg3.add(word_acbaa);
		dawg3 = dawg3.add(word_acbcb);
		dawg3 = dawg3.add(word_babaa);
		dawg3 = dawg3.add(word_babcb);
		dawg3 = dawg3.add(word_aacab);

		Dawg<String, String> dawg4 = new ReorderAndRenameDawgBuilder<String, String>(
					dawgFactoryStringString, 
					(Dawg<String, String>) dawg3, 
					"v", 
					"y")
				.build();
		
		assertTrue(dawg4.accepts(word_aaaaa));
		assertTrue(dawg4.accepts(word_acbab));
		assertTrue(dawg4.accepts(word_abaca));
		assertTrue(dawg4.accepts(word_accac));
		assertTrue(dawg4.accepts(word_abccb));
		assertTrue(dawg4.accepts(word_bbaaa));
		assertTrue(dawg4.accepts(word_bbcab));
	}
	
	/**
	 * Example for RenameAndReorder which
	 *  - moves from left to right
	 *  - source column is at the very start
	 *  - target column is not at the very end
	 * 
	 *  (example from the whiteboard in Jan/Feb 2017)
	 */
	@Test
	public void test3() {
		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory(), getAllConstants());
		
		SortedSet<String> signaturePre = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePre.addAll(Arrays.asList(new String[] { "u", "v", "x"}));
		
		SortedSet<String> signaturePost = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePost.addAll(Arrays.asList(new String[] { "v", "w", "x"}));
	

		/*
		 * word in the original automaton
		 */
		List<String> word_aaa = Arrays.asList(new String[] { "a", "a", "a" });
		List<String> word_abb = Arrays.asList(new String[] { "a", "b", "b" });
		List<String> word_abc = Arrays.asList(new String[] { "a", "b", "c" });
		List<String> word_caa = Arrays.asList(new String[] { "c", "a", "a" });

		/*
		 * words that should be in the transformed automaton
		 */
		List<String> word_bab = Arrays.asList(new String[] { "b", "a", "b" });
		List<String> word_bac = Arrays.asList(new String[] { "b", "a", "c" });
		List<String> word_aca = Arrays.asList(new String[] { "a", "c", "a" });


	
		dawg3 = dawgFactoryStringString.getEmptyDawg(signaturePre);
		dawg3 = dawg3.add(word_aaa);
		dawg3 = dawg3.add(word_abb);
		dawg3 = dawg3.add(word_abc);
		dawg3 = dawg3.add(word_caa);

		Dawg<String, String> dawg4 = new ReorderAndRenameDawgBuilder<String, String>(
					dawgFactoryStringString, 
					(Dawg<String, String>) dawg3, 
					"u", 
					"w")
				.build();
		
		assertTrue(dawg4.accepts(word_aaa));
		assertTrue(dawg4.accepts(word_bab));
		assertTrue(dawg4.accepts(word_bac));
		assertTrue(dawg4.accepts(word_aca));
	}
	
	/**
	 * Example for RenameAndReorder which
	 *  - moves from right to left
	 *  - source column is not at the very start
	 *  - target column is not at the very end
	 * 
	 *  (the inverse transformation of test2)
	 */
	@Test
	public void test4() {
		Set<String> allConstants = new HashSet<String>(Arrays.asList(new String[] { "a", "b", "c", "d", "e" }));
		
		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory(), allConstants);

		/*
		 * words in the original automaton
		 */
		List<String> word_abcde = Arrays.asList(new String[] { "a", "b", "c", "d", "e" });

		/*
		 * words that should be in the transformed automaton
		 */
		List<String> word_adbce = Arrays.asList(new String[] { "a", "d", "b", "c", "e" });

		SortedSet<String> signature3 = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signature3.addAll(Arrays.asList(new String[] { "u", "w", "x", "y", "z" }));
		
		SortedSet<String> signature4 = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signature4.addAll(Arrays.asList(new String[] { "u", "v", "w", "x", "z"}));
		
		dawg3 = dawgFactoryStringString.getEmptyDawg(signature3);
		dawg3 = dawg3.add(word_abcde);

		Dawg<String, String> dawg4 = new ReorderAndRenameDawgBuilder<String, String>(
					dawgFactoryStringString, 
					(Dawg<String, String>) dawg3, 
					"y", 
					"v")
				.build();

		assertTrue(dawg4.accepts(word_adbce));
		
	}
	
	
		/**
	 * Example for RenameAndReorder which
	 *  - moves from right to left
	 *  - source column is not at the very start
	 *  - target column is not at the very end
	 * 
	 *  (the inverse transformation of test2)
	 */
	@Test
	public void test5() {
		
		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory(), getAllConstants());

		/*
		 * words in the original automaton
		 */
		List<String> word_aaaaa = Arrays.asList(new String[] { "a", "a", "a", "a", "a" });
		List<String> word_aaacb = Arrays.asList(new String[] { "a", "a", "a", "c", "b" });
		List<String> word_aacbb = Arrays.asList(new String[] { "a", "a", "c", "b", "b" });
		List<String> word_aaccc = Arrays.asList(new String[] { "a", "a", "c", "c", "c" });
		List<String> word_acbaa = Arrays.asList(new String[] { "a", "c", "b", "a", "a" });
		List<String> word_acbcb = Arrays.asList(new String[] { "a", "c", "b", "c", "b" });
		List<String> word_babaa = Arrays.asList(new String[] { "b", "a", "b", "a", "a" });
		List<String> word_babcb = Arrays.asList(new String[] { "b", "a", "b", "c", "b" });
		List<String> word_aacab = Arrays.asList(new String[] { "a", "a", "c", "a", "b" });

		/*
		 * words that should be in the transformed automaton
		 */
		List<String> word_acaab = Arrays.asList(new String[] { "a", "c", "a", "a", "b" });
		List<String> word_abacb = Arrays.asList(new String[] { "a", "b", "a", "c", "b" });
		List<String> word_acacc = Arrays.asList(new String[] { "a", "c", "a", "c", "c" });
		List<String> word_aacba = Arrays.asList(new String[] { "a", "a", "c", "b", "a" });
		List<String> word_accbb = Arrays.asList(new String[] { "a", "c", "c", "b", "b" });
		List<String> word_baaba = Arrays.asList(new String[] { "b", "a", "a", "b", "a" });
		List<String> word_bcabb = Arrays.asList(new String[] { "b", "c", "a", "b", "b" });
	
		SortedSet<String> signature3 = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signature3.addAll(Arrays.asList(new String[] { "u", "w", "x", "y", "z" }));
		
		SortedSet<String> signature4 = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signature4.addAll(Arrays.asList(new String[] { "u", "v", "w", "x", "z"}));
		
		dawg3 = dawgFactoryStringString.getEmptyDawg(signature3);
		dawg3 = dawg3.add(word_aaaaa);
		dawg3 = dawg3.add(word_aaacb);
		dawg3 = dawg3.add(word_aacbb);
		dawg3 = dawg3.add(word_aaccc);

		dawg3 = dawg3.add(word_acbaa);
		dawg3 = dawg3.add(word_acbcb);
		dawg3 = dawg3.add(word_babaa);
		dawg3 = dawg3.add(word_babcb);
		dawg3 = dawg3.add(word_aacab);

		Dawg<String, String> dawg4 = new ReorderAndRenameDawgBuilder<String, String>(
					dawgFactoryStringString, 
					(Dawg<String, String>) dawg3, 
					"y", 
					"v")
				.build();
		
		assertTrue(dawg4.accepts(word_aaaaa));
		assertTrue(dawg4.accepts(word_acaab));
		assertTrue(dawg4.accepts(word_abacb));
		assertTrue(dawg4.accepts(word_acacc));
		assertTrue(dawg4.accepts(word_aacba));
		assertTrue(dawg4.accepts(word_accbb));
		assertTrue(dawg4.accepts(word_baaba));
		assertTrue(dawg4.accepts(word_bcabb));
	}
	
	/**
	 * Example for RenameAndReorder which
	 *  - moves from right to left
	 *  - source column is at the very end
	 *  - target column is not at the very start
	 * 
	 */
	@Test
	public void test6() {
		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory(), getAllConstants());
		
		SortedSet<String> signaturePre = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePre.addAll(Arrays.asList(new String[] { "u", "w", "x"}));
		
		SortedSet<String> signaturePost = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePost.addAll(Arrays.asList(new String[] { "u", "v", "w"}));
	

		/*
		 * word in the original automaton
		 */
		List<String> word_abc = Arrays.asList(new String[] { "a", "b", "c" });

		/*
		 * words that should be in the transformed automaton
		 */
		List<String> word_acb = Arrays.asList(new String[] { "a", "c", "b" });


		dawg3 = dawgFactoryStringString.getEmptyDawg(signaturePre);
		dawg3 = dawg3.add(word_abc);

		Dawg<String, String> dawg4 = new ReorderAndRenameDawgBuilder<String, String>(
					dawgFactoryStringString, 
					(Dawg<String, String>) dawg3, 
					"x", 
					"v")
				.build();
		
		assertTrue(dawg4.accepts(word_acb));
	}
	
		/**
	 * Example for RenameAndReorder which
	 *  - moves from right to left
	 *  - source column is at the very end
	 *  - target column is not at the very start
	 * 
	 */
	@Test
	public void test7() {
		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory(), getAllConstants());
		
		SortedSet<String> signaturePre = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePre.addAll(Arrays.asList(new String[] { "u", "w", "x"}));
		
		SortedSet<String> signaturePost = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePost.addAll(Arrays.asList(new String[] { "u", "v", "w"}));
	

		/*
		 * word in the original automaton
		 */
		List<String> word_aaa = Arrays.asList(new String[] { "a", "a", "a" });
		List<String> word_bba = Arrays.asList(new String[] { "b", "b", "a" });
		List<String> word_abc = Arrays.asList(new String[] { "a", "b", "c" });
		List<String> word_aac = Arrays.asList(new String[] { "a", "a", "c" });

		/*
		 * words that should be in the transformed automaton
		 */
		List<String> word_bab = Arrays.asList(new String[] { "b", "a", "b" });
		List<String> word_acb = Arrays.asList(new String[] { "a", "c", "b" });
		List<String> word_aca = Arrays.asList(new String[] { "a", "c", "a" });


		dawg3 = dawgFactoryStringString.getEmptyDawg(signaturePre);
		dawg3 = dawg3.add(word_aaa);
		dawg3 = dawg3.add(word_bba);
		dawg3 = dawg3.add(word_abc);
		dawg3 = dawg3.add(word_aac);

		Dawg<String, String> dawg4 = new ReorderAndRenameDawgBuilder<String, String>(
					dawgFactoryStringString, 
					(Dawg<String, String>) dawg3, 
					"x", 
					"v")
				.build();
		
		assertTrue(dawg4.accepts(word_aaa));
		assertTrue(dawg4.accepts(word_bab));
		assertTrue(dawg4.accepts(word_acb));
		assertTrue(dawg4.accepts(word_aca));
	}
}
