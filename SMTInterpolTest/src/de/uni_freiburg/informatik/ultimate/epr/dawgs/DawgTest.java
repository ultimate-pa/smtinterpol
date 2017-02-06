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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

@RunWith(JUnit4.class)
public class DawgTest {
	
	private IDawg<String, Integer> dawg1;
	private TreeSet<Integer> signature1;
	private List<String> word1;
	private IDawg<String, Integer> dawg2;
	private List<String> word3;
	private List<String> word4;
	private List<String> word5;
	private List<String> word6;
	private List<String> word7;
	private List<String> word8;
	private List<String> word9;
	private IDawg<String, Integer> dawg3;
	private List<String> word2;
	private IDawg<String, Integer> dawg4;
	private IDawg<String, Integer> dawg5;
	private IDawg<String, Integer> dawg6;

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
		
		DawgFactory<String, Integer> dawgFactory = 
				new DawgFactory<String, Integer>(getEprTheory(), getAllConstants());

		signature1 = new TreeSet<Integer>(Arrays.asList(new Integer[] { 1, 2 }));
		dawg1 = dawgFactory.getEmptyDawg(signature1);
		
		word1 = Arrays.asList(new String[] { "a", "a" });
		dawg2 = dawg1.add(word1);

		word2 = Arrays.asList(new String[] { "a", "b" });
		
		word3 = Arrays.asList(new String[] { "a", "c" });
		word4 = Arrays.asList(new String[] { "b", "a" });
		word5 = Arrays.asList(new String[] { "b", "b" });
		word6 = Arrays.asList(new String[] { "b", "c" });
		word7 = Arrays.asList(new String[] { "c", "a" });
		word8 = Arrays.asList(new String[] { "c", "b" });
		word9 = Arrays.asList(new String[] { "c", "c" });

		dawg3 = dawg2.add(word2);
		dawg3 = dawg3.add(word3);
		dawg3 = dawg3.add(word4);
		dawg3 = dawg3.add(word5);
		dawg3 = dawg3.add(word6);
		dawg3 = dawg3.add(word7);
		dawg3 = dawg3.add(word8);
		dawg3 = dawg3.add(word9);
		
		dawg4 = dawg2.add(word2);
		dawg4 = dawg4.add(word3);
		
		dawg5 = dawg4.add(word4);
//		dawg5 = dawg5.add(word5);
//		dawg5 = dawg5.add(word6);
//		dawg5 = dawg5.add(word7);
		
		dawg6 = dawg3.complement();
	}

	@Test
	public void testDawg1() {
		assertTrue(dawg1.isEmpty());
		assertFalse(dawg1.isUniversal());
	}

	@Test
	public void testDawg2() {
		assertFalse(dawg2.isEmpty());
		assertFalse(dawg2.isUniversal());
		assertTrue(dawg2.accepts(word1));
		assertFalse(dawg2.accepts(word2));
		assertTrue(dawg2.isSingleton());
	}

	@Test
	public void testDawg3() {
		assertTrue(dawg3.isUniversal());
	}

	@Test
	public void testDawg4() {
		assertTrue(dawg4.accepts(word2));
		assertTrue(dawg4.accepts(word3));
		assertFalse(dawg4.accepts(word4));
	}
	
	@Test
	public void testDawg5() {
		dawg5.listPoints();
		assertTrue(dawg5.accepts(word1));
		assertTrue(dawg5.accepts(word4));
//		assertTrue(dawg5.accepts(word5));
//		assertTrue(dawg5.accepts(word6));
	}
	
	@Test
	public void testDawg6() {
		assertTrue(dawg6.isEmpty());
	}
}

class EprTheoryMock extends EprTheory {
	public EprTheoryMock(LogProxy logger) {
		super(logger);
	}
}