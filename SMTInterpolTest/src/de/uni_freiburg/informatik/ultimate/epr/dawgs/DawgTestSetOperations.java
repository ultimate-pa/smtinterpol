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
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

/**
 * Tests for the standard set operations on dawgs.
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
@RunWith(JUnit4.class)
public class DawgTestSetOperations {
	
	private IDawg<String, Integer> dawg1;
	private TreeSet<Integer> signature1;
	private List<String> word_aa;
	private IDawg<String, Integer> dawg2;
	private List<String> word_ac;
	private List<String> word_ba;
	private List<String> word_bb;
	private List<String> word_bc;
	private List<String> word_ca;
	private List<String> word_cb;
	private List<String> word_cc;
	private IDawg<String, Integer> dawg3;
	private List<String> word_ab;
	private IDawg<String, Integer> dawg4;
	private IDawg<String, Integer> dawg5;
	private IDawg<String, Integer> dawg6;
	private IDawg<String, Integer> dawg7;
	private IDawg<String, Integer> dawg8;
	private IDawg<String, Integer> dawg9;
	private IDawg<String, Integer> dawg10;
	private IDawg<String, Integer> dawg11;
	private IDawg<String, Integer> dawg12;
	private IDawg<String, Integer> dawg13;
	private IDawg<String, Integer> dawg14;




	@Before
	public void setup() {
		
		DawgFactory<String, Integer> dawgFactory = 
				new DawgFactory<String, Integer>(EprTestHelpers.getEprTheory());
		EprTestHelpers.addConstantsWDefaultSort(dawgFactory, EprTestHelpers.constantsAbc());

		signature1 = new TreeSet<Integer>(Arrays.asList(new Integer[] { 1, 2 }));
		dawg1 = dawgFactory.getEmptyDawg(signature1);
		
		word_aa = Arrays.asList(new String[] { "a", "a" });
		dawg2 = dawg1.add(word_aa);

		word_ab = Arrays.asList(new String[] { "a", "b" });
		
		word_ac = Arrays.asList(new String[] { "a", "c" });
		word_ba = Arrays.asList(new String[] { "b", "a" });
		word_bb = Arrays.asList(new String[] { "b", "b" });
		word_bc = Arrays.asList(new String[] { "b", "c" });
		word_ca = Arrays.asList(new String[] { "c", "a" });
		word_cb = Arrays.asList(new String[] { "c", "b" });
		word_cc = Arrays.asList(new String[] { "c", "c" });

		dawg3 = dawg2.add(word_ab);
		dawg3 = dawg3.add(word_ac);
		dawg3 = dawg3.add(word_ba);
		dawg3 = dawg3.add(word_bb);
		dawg3 = dawg3.add(word_bc);
		dawg3 = dawg3.add(word_ca);
		dawg3 = dawg3.add(word_cb);
		dawg7 = dawgFactory.copyDawg(dawg3);
		dawg3 = dawg3.add(word_cc);
		
		dawg4 = dawg2.add(word_ab);
		dawg4 = dawg4.add(word_ac);
		
		dawg5 = dawg4.add(word_ba);
//		dawg5 = dawg5.add(word5);
//		dawg5 = dawg5.add(word6);
//		dawg5 = dawg5.add(word7);
		
		dawg6 = dawg3.complement();
		
		dawg8 = dawg7.complement();
//		dawg8 = null;
		
		dawg9 = dawgFactory.getEmptyDawg(signature1);
		dawg9 = dawg9.add(word_aa);
		dawg9 = dawg9.add(word_ab);
		
		dawg10 = dawgFactory.getEmptyDawg(signature1);
		dawg10 = dawg10.add(word_ab);
		dawg10 = dawg10.add(word_ac);
		
		dawg11 = dawg9.intersect(dawg10);
		
		dawg12 = dawg11.complement();
		dawg12 = dawg12.add(word_ab);
		
		dawg13 = dawgFactory.createOnePointDawg(signature1, word_ba);
		dawg13 = dawg13.add(word_bb);
		dawg13 = dawg13.add(word_bc);
		dawg13 = dawg13.add(word_ca);
		dawg13 = dawg13.add(word_cb);
		dawg13 = dawg13.add(word_cc);

		
		dawg14 = dawg9.union(dawg10);
		dawg14 = dawg14.union(dawg13);

	}

	@Test
	public void testDawg1() {
		assertFalse(dawg1.iterator().hasNext());
		assertTrue(dawg1.isEmpty());
		assertFalse(dawg1.isUniversal());
	}

	@Test
	public void testDawg2() {
		assertFalse(dawg2.isEmpty());
		assertFalse(dawg2.isUniversal());
		assertTrue(dawg2.accepts(word_aa));
		assertFalse(dawg2.accepts(word_ab));
		assertTrue(dawg2.isSingleton());
	}

	@Test
	public void testDawg3() {
//		assertTrue(dawg3.isUniversal()); // changed meaning of universal (to be independent from allConstants)
	}

	@Test
	public void testDawg4() {
		assertTrue(dawg4.accepts(word_ab));
		assertTrue(dawg4.accepts(word_ac));
		assertFalse(dawg4.accepts(word_ba));
	}
	
	@Test
	public void testDawg5() {
		assertTrue(dawg5.accepts(word_aa));
		assertTrue(dawg5.accepts(word_ba));
//		assertTrue(dawg5.accepts(word5));
//		assertTrue(dawg5.accepts(word6));
	}
	
	@Test
	public void testDawg6() {
//		assertTrue(dawg6.isEmpty()); // not empty by new AllConstants convention!
	}
	
	@Test
	public void testDawg7() {
		assertFalse(dawg7.isEmpty());
		assertFalse(dawg7.isUniversal());
		assertFalse(dawg7.isSingleton());
		assertFalse(dawg7.accepts(word_cc));
	}
	
	@Test
	public void testDawg8() {
//		assertTrue(dawg8.isSingleton()); // not singleton by new AllConstants convention!
		assertTrue(dawg8.accepts(word_cc));
	}
	
	@Test
	public void testDawg11() {
//		assertTrue(dawg11.isSingleton()); // not singleton by new AllConstants convention!
		assertTrue(dawg11.accepts(word_ab));
	}

	@Test
	public void testDawg12() {
		assertTrue(dawg12.isUniversal());
	}
	
	@Test
	public void testDawg13() {
//		assertTrue(dawg14.isUniversal()); // not universal by new AllConstants convention!
	}

	/**
	 * tests complement operation
	 */
	@Test
	public void test14() {
		
		final DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(EprTestHelpers.getEprTheory());
		EprTestHelpers.addConstantsWDefaultSort(dawgFactoryStringString, EprTestHelpers.constantsAbc());
	
		/*
		 * words in the first automaton
		 */
		final List<String> word_aa = Arrays.asList(new String[] { "a", "a" });
		
		/*
		 * words not in the first automaton
		 */
		final List<String> word_ab = Arrays.asList(new String[] { "a", "b" });
		final List<String> word_bb = Arrays.asList(new String[] { "b", "b" });

		final SortedSet<String> signature = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signature.addAll(Arrays.asList(new String[] { "u", "w" }));
		
		final IDawg<String, String> dawgPre = dawgFactoryStringString.createOnePointDawg(signature, word_aa);
		
		assertTrue(dawgPre.accepts(word_aa));
		assertFalse(dawgPre.accepts(word_ab));
		assertFalse(dawgPre.accepts(word_bb));


		final IDawg<String, String> dawgPost = dawgPre.complement();

		assertFalse(dawgPost.accepts(word_aa));
		assertTrue(dawgPost.accepts(word_ab));
		assertTrue(dawgPost.accepts(word_bb));
	}
}

class EprTheoryMock extends EprTheory {
	public EprTheoryMock(LogProxy logger) {
		super(logger);
	}
}