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
	private Object dawg2;
	private List<String> word_aaaaa;
	private List<String> word_aaacb;
	private List<String> word_aacbb;
	private List<String> word_aaccc;
	private List<String> word_acbaa;
	private List<String> word_acbcb;
	private List<String> word_babaa;
	private List<String> word_babcb;
	private IDawg<String, String> dawg3;
	private List<String> word_aacab;
	private List<String> word_acbab;
	private List<String> word_accac;

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

	@Before
	public void setup() {
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
				
		SortedSet<Integer> signature2 = new TreeSet<Integer>(EprHelpers.getColumnNamesComparator());
		signature2.addAll(Arrays.asList(new Integer[] { 10, 20, 30 }));

		BinaryRelation<Integer, Integer> translation1 = new BinaryRelation<Integer, Integer>();
		translation1.addPair(1, 20);
		translation1.addPair(1, 30);
		translation1.addPair(2, 10);

		List<Object> argList1 = Arrays.asList(new Object[] { 1, 1, 2 });
		

//		dawg2 = dawg1.translateClauseSigToPredSig(translation1, argList1, signature2);
				
	}
	
	@Test
	public void test1() {
		assertTrue(dawg1.accepts(word_ba));
		assertTrue(dawg1.accepts(word_ca));
		
	}
	
	@Test
	public void test2() {
		/*
		 *  example from the whiteboard
		 *   --> not the smallest example but should avoid special cases like "move first column"
		 */
		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory(), getAllConstants());

		word_aaaaa = Arrays.asList(new String[] { "a", "a", "a", "a", "a" });
		word_aaacb = Arrays.asList(new String[] { "a", "a", "a", "c", "b" });
		word_aacbb = Arrays.asList(new String[] { "a", "a", "c", "b", "b" });
		word_aaccc = Arrays.asList(new String[] { "a", "a", "c", "c", "c" });
		word_acbaa = Arrays.asList(new String[] { "a", "c", "b", "a", "a" });
		word_acbcb = Arrays.asList(new String[] { "a", "c", "b", "c", "b" });
		word_babaa = Arrays.asList(new String[] { "b", "a", "b", "a", "a" });
		word_babcb = Arrays.asList(new String[] { "b", "a", "b", "c", "b" });

		word_aacab = Arrays.asList(new String[] { "a", "a", "c", "a", "b" });
		word_acbab = Arrays.asList(new String[] { "a", "c", "b", "a", "b" });
		word_accac = Arrays.asList(new String[] { "a", "c", "c", "a", "c" });
		
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
		assertTrue(dawg4.accepts(word_accac));
		
	}
	
}
