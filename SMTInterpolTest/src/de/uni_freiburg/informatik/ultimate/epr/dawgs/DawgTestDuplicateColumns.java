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

import static org.junit.Assert.*;

import java.util.Arrays;
import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.Dawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgbuilders.ReorderAndRenameDawgBuilder;

public class DawgTestDuplicateColumns {
	
	private EprTheory getEprTheory() {
		return new EprTheoryMock(getLogger());
	}
	
	private LogProxy getLogger() {
		return new DefaultLogger();
	}
	
	/**
	 * Example for RenameAndReorder in duplication mode
	 *  - moves from left to right
	 *  - source column is in the middle
	 *  - target column is at the very end
	 *  - just one word in the language
	 * 
	 */
	@Test
	public void test8() {
		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory());
		

		EprTestHelpers.addConstantsWDefaultSort(dawgFactoryStringString, EprTestHelpers.constantsAbc());
//		dawgFactoryStringString.addConstants(getAllConstants());
		
		SortedSet<String> signaturePre = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePre.addAll(Arrays.asList(new String[] { "u", "v"}));
		
		SortedSet<String> signaturePost = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePost.addAll(Arrays.asList(new String[] { "u", "v", "w"}));
	

		/*
		 * word in the original automaton
		 */
		List<String> word_ab = Arrays.asList(new String[] { "a", "b" });

		/*
		 * words that should be in the transformed automaton
		 */
		List<String> word_abb = Arrays.asList(new String[] { "a", "b", "b" });


		IDawg<String, String> dawg3 = dawgFactoryStringString.getEmptyDawg(signaturePre);
		dawg3 = dawg3.add(word_ab);

		Dawg<String, String> dawg4 = new ReorderAndRenameDawgBuilder<String, String>(
					dawgFactoryStringString, 
					(Dawg<String, String>) dawg3, 
					"v", 
					"w",
					true)
				.build();
		
		assertTrue(dawg4.getColNames().equals(signaturePost));
		assertTrue(dawg4.accepts(word_abb));
	}
	
	
	/**
	 * Example for RenameAndReorder in duplication mode
	 *  - moves from right to left
	 *  - source column is at the very end
	 *  - target column is in the middle
	 *  - just one word in the language
	 * 
	 */
	@Test
	public void test9() {
		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory());

		EprTestHelpers.addConstantsWDefaultSort(dawgFactoryStringString, EprTestHelpers.constantsAbc());
//		dawgFactoryStringString.addConstants(getAllConstants());
		
		SortedSet<String> signaturePre = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePre.addAll(Arrays.asList(new String[] { "u", "w"}));
		
		SortedSet<String> signaturePost = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePost.addAll(Arrays.asList(new String[] { "u", "v", "w"}));

		/*
		 * word in the original automaton
		 */
		List<String> word_ab = Arrays.asList(new String[] { "a", "b" });

		/*
		 * words that should be in the transformed automaton
		 */
		List<String> word_abb = Arrays.asList(new String[] { "a", "b", "b" });


		IDawg<String, String> dawg3 = dawgFactoryStringString.getEmptyDawg(signaturePre);
		dawg3 = dawg3.add(word_ab);

		Dawg<String, String> dawg4 = new ReorderAndRenameDawgBuilder<String, String>(
					dawgFactoryStringString, 
					(Dawg<String, String>) dawg3, 
					"w", 
					"v",
					true)
				.build();
		
		assertTrue(dawg4.getColNames().equals(signaturePost));
		assertTrue(dawg4.accepts(word_abb));
	}
	
	
		/**
	 * Example for RenameAndReorder in duplication mode
	 *  - moves from left to right
	 *  - source column is in the middle
	 *  - target column is at the very end
	 *  - more than one word in the language
	 * 
	 */
	@Test
	public void test10() {
		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory());
		
		SortedSet<String> signaturePre = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePre.addAll(Arrays.asList(new String[] { "u", "v"}));
		
		SortedSet<String> signaturePost = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePost.addAll(Arrays.asList(new String[] { "u", "v", "w"}));
	

		/*
		 * word in the original automaton
		 */
		List<String> word_ab = Arrays.asList(new String[] { "a", "b" });
		List<String> word_ba = Arrays.asList(new String[] { "b", "a" });
		List<String> word_bb = Arrays.asList(new String[] { "b", "b" });

		/*
		 * words that should be in the transformed automaton
		 */
		List<String> word_abb = Arrays.asList(new String[] { "a", "b", "b" });
		List<String> word_baa = Arrays.asList(new String[] { "b", "a", "a" });
		List<String> word_bbb = Arrays.asList(new String[] { "b", "b", "b" });


		IDawg<String, String> dawg3 = dawgFactoryStringString.getEmptyDawg(signaturePre);
		dawg3 = dawg3.add(word_ab);
		dawg3 = dawg3.add(word_ba);
		dawg3 = dawg3.add(word_bb);

		Dawg<String, String> dawg4 = new ReorderAndRenameDawgBuilder<String, String>(
					dawgFactoryStringString, 
					(Dawg<String, String>) dawg3, 
					"v", 
					"w",
					true)
				.build();
		
		assertTrue(dawg4.getColNames().equals(signaturePost));
		assertTrue(dawg4.accepts(word_abb));
		assertTrue(dawg4.accepts(word_baa));
		assertTrue(dawg4.accepts(word_bbb));
	}
	
	
	/**
	 * Example for RenameAndReorder in duplication mode
	 *  - moves from right to left
	 *  - source column is at the very end
	 *  - target column is in the middle
	 *  - more than one word in the language
	 * 
	 */
	@Test
	public void test11() {
		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory());

		EprTestHelpers.addConstantsWDefaultSort(dawgFactoryStringString, EprTestHelpers.constantsAbc());
//		dawgFactoryStringString.addConstants(getAllConstants());

		SortedSet<String> signaturePre = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePre.addAll(Arrays.asList(new String[] { "u", "w"}));
		
		SortedSet<String> signaturePost = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePost.addAll(Arrays.asList(new String[] { "u", "v", "w"}));

		/*
		 * word in the original automaton
		 */
		List<String> word_ab = Arrays.asList(new String[] { "a", "b" });
		List<String> word_ba = Arrays.asList(new String[] { "b", "a" });
		List<String> word_bb = Arrays.asList(new String[] { "b", "b" });

		/*
		 * words that should be in the transformed automaton
		 */
		List<String> word_abb = Arrays.asList(new String[] { "a", "b", "b" });
		List<String> word_baa = Arrays.asList(new String[] { "b", "a", "a" });
		List<String> word_bbb = Arrays.asList(new String[] { "b", "b", "b" });


		IDawg<String, String> dawg3 = dawgFactoryStringString.getEmptyDawg(signaturePre);
		dawg3 = dawg3.add(word_ab);
		dawg3 = dawg3.add(word_ba);
		dawg3 = dawg3.add(word_bb);

		Dawg<String, String> dawg4 = new ReorderAndRenameDawgBuilder<String, String>(
					dawgFactoryStringString, 
					(Dawg<String, String>) dawg3, 
					"w", 
					"v",
					true)
				.build();
		
		assertTrue(dawg4.getColNames().equals(signaturePost));
		assertTrue(dawg4.accepts(word_abb));
		assertTrue(dawg4.accepts(word_baa));
		assertTrue(dawg4.accepts(word_bbb));

	}
	
	
	/**
	 * Example for RenameAndReorder in duplication mode
	 *  aimed to check that edges with set-DawgLetters are split up correctly 
	 *   (e.g. an edge that could be taken with {a,b} that is duplicated does not lead to (a b) being accepted)
	 * 
	 */
	@Test
	public void test12() {
		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory());

		EprTestHelpers.addConstantsWDefaultSort(dawgFactoryStringString, EprTestHelpers.constantsAbc());

		SortedSet<String> signaturePre = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePre.addAll(Arrays.asList(new String[] { "u",}));
		
		SortedSet<String> signaturePost = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePost.addAll(Arrays.asList(new String[] { "u", "v"}));

		/*
		 * word in the original automaton
		 */
		List<String> word_a = Arrays.asList(new String[] { "a" });
		List<String> word_b = Arrays.asList(new String[] { "b" });
		List<String> word_c = Arrays.asList(new String[] { "c" });

		/*
		 * words that should be in the transformed automaton
		 */
		List<String> word_aa = Arrays.asList(new String[] { "a", "a" });
		List<String> word_bb = Arrays.asList(new String[] { "b", "b" });

		/*
		 * words that should not be in the transformed automaton
		 */
		List<String> word_ab = Arrays.asList(new String[] { "a", "b" });
		List<String> word_ba = Arrays.asList(new String[] { "b", "a" });


		IDawg<String, String> dawgPre = dawgFactoryStringString.getUniversalDawg(signaturePre);
		
		assertTrue(dawgPre.accepts(word_a));
		assertTrue(dawgPre.accepts(word_b));
		assertTrue(dawgPre.accepts(word_c));
		

		Dawg<String, String> dawgPost = new ReorderAndRenameDawgBuilder<String, String>(
					dawgFactoryStringString, 
					(Dawg<String, String>) dawgPre, 
					"u", 
					"v",
					true)
				.build();
		
		assertTrue(dawgPost.getColNames().equals(signaturePost));
		assertTrue(dawgPost.accepts(word_aa));
		assertTrue(dawgPost.accepts(word_bb));
		assertFalse(dawgPost.accepts(word_ab));
		assertFalse(dawgPost.accepts(word_ba));

	}
}
