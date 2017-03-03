package de.uni_freiburg.informatik.ultimate.epr.dawgs;

import static org.junit.Assert.*;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.ReorderAndRenameDawgBuilder;

public class DawgTestMergeColumns {

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
	
	/**
	 * Example for RenameAndReorder in merge mode
	 *  - moves from left to right
	 *  - source column is not at the very start
	 *  - target column is not at the very end
	 *  - just one word in pre dawg
	 *  - no word expected in post dawg
	 * 
	 */
	@Test
	public void test1a() {
		Set<String> allConstants = new HashSet<String>(Arrays.asList(new String[] { "a", "b", "c", "d", "e" }));

		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory());
		dawgFactoryStringString.addConstants(allConstants);

		/*
		 * words in the original automaton
		 */
		List<String> word_abcde = Arrays.asList(new String[] { "a", "b", "c", "d", "e" });

		/*
		 * words that should be in the transformed automaton
		 */
		SortedSet<String> signature3 = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signature3.addAll(Arrays.asList(new String[] { "u", "v", "w", "x", "z"}));

		SortedSet<String> signature4 = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signature4.addAll(Arrays.asList(new String[] { "u", "w", "x", "z"}));

		IDawg<String, String> dawg3 = dawgFactoryStringString.getEmptyDawg(signature3);
		dawg3 = dawg3.add(word_abcde);


		Dawg<String, String> dawg4 = new ReorderAndRenameDawgBuilder<String, String>(
				dawgFactoryStringString, 
				(Dawg<String, String>) dawg3, 
				"v", 
				"x",
				false,
				true)
				.build();

		assertTrue(dawg4.getColnames().equals(signature4));
		assertTrue(dawg4.isEmpty());
	}
	
	/**
	 * Example for RenameAndReorder in merge mode
	 *  - moves from left to right
	 *  - source column is not at the very start
	 *  - target column is not at the very end
	 *  - just one word in pre dawg
	 *  - one word expected in post dawg
	 * 
	 */
	@Test
	public void test1b() {
		Set<String> allConstants = new HashSet<String>(Arrays.asList(new String[] { "a", "b", "c", "d", "e" }));

		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory());
		dawgFactoryStringString.addConstants(allConstants);

		/*
		 * words in the original automaton
		 */
		List<String> word_abcbe = Arrays.asList(new String[] { "a", "b", "c", "b", "e" });

		/*
		 * words that should be in the transformed automaton
		 */
		List<String> word_acbe = Arrays.asList(new String[] { "a", "c", "b", "e" });

		SortedSet<String> signature3 = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signature3.addAll(Arrays.asList(new String[] { "u", "v", "w", "x", "z"}));

		SortedSet<String> signature4 = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signature4.addAll(Arrays.asList(new String[] { "u", "w", "x", "z"}));

		IDawg<String, String> dawg3 = dawgFactoryStringString.getEmptyDawg(signature3);
		dawg3 = dawg3.add(word_abcbe);


		Dawg<String, String> dawg4 = new ReorderAndRenameDawgBuilder<String, String>(
				dawgFactoryStringString, 
				(Dawg<String, String>) dawg3, 
				"v", 
				"x",
				false,
				true)
				.build();

		assertTrue(dawg4.getColnames().equals(signature4));
		assertTrue(dawg4.accepts(word_acbe));
	}
	
	
	/**
	 * Example for RenameAndReorder in merge mode
	 *  - moves from left to right
	 *  - source column is not at the very start
	 *  - target column is not at the very end
	 * 
	 */
	@Test
	public void test1() {
		Set<String> allConstants = new HashSet<String>(Arrays.asList(new String[] { "a", "b", "c", "d", "e" }));
		
		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory());
		dawgFactoryStringString.addConstants(allConstants);


		/*
		 * words in the original automaton
		 */
		List<String> word_abcde = Arrays.asList(new String[] { "a", "b", "c", "d", "e" });
		List<String> word_abcbe = Arrays.asList(new String[] { "a", "b", "c", "b", "e" });
		List<String> word_cccca = Arrays.asList(new String[] { "c", "c", "c", "c", "a" });
		List<String> word_caaac = Arrays.asList(new String[] { "c", "a", "a", "a", "c" });
		List<String> word_caabb = Arrays.asList(new String[] { "c", "a", "a", "b", "b" });

		/*
		 * words that should be in the transformed automaton
		 */
		List<String> word_acbe = Arrays.asList(new String[] { "a", "c", "b", "e" });
		List<String> word_ccca = Arrays.asList(new String[] { "c", "c", "c", "a" });
		List<String> word_caac = Arrays.asList(new String[] { "c", "a", "a", "c" });

		SortedSet<String> signature3 = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signature3.addAll(Arrays.asList(new String[] { "u", "v", "w", "x", "z"}));
		
		SortedSet<String> signature4 = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signature4.addAll(Arrays.asList(new String[] { "u", "w", "x", "z"}));
		
		IDawg<String, String> dawg3 = dawgFactoryStringString.getEmptyDawg(signature3);
		dawg3 = dawg3.add(word_abcde);
		dawg3 = dawg3.add(word_abcbe);
		dawg3 = dawg3.add(word_cccca);
		dawg3 = dawg3.add(word_caaac);
		dawg3 = dawg3.add(word_caabb);


		Dawg<String, String> dawg4 = new ReorderAndRenameDawgBuilder<String, String>(
					dawgFactoryStringString, 
					(Dawg<String, String>) dawg3, 
					"v", 
					"x",
					false,
					true)
				.build();

		assertTrue(dawg4.getColnames().equals(signature4));
		assertTrue(dawg4.accepts(word_acbe));
		assertTrue(dawg4.accepts(word_ccca));
		assertTrue(dawg4.accepts(word_caac));
	}
	

	/**
	 * Example for merging two columns
	 *  - moves from left to right
	 *  - source column is in the middle
	 *  - target column is at the very end
	 */
	@Test
	public void test2() {
		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory());
		dawgFactoryStringString.addConstants(getAllConstants());
		
		SortedSet<String> signaturePre = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePre.addAll(Arrays.asList(new String[] { "u", "v", "w"}));
		
		SortedSet<String> signaturePost = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePost.addAll(Arrays.asList(new String[] { "u", "w" }));
	

		/*
		 * word in the original automaton
		 */
		List<String> word_aaa = Arrays.asList(new String[] { "a", "a", "a" });
		List<String> word_abb = Arrays.asList(new String[] { "a", "b", "b" });
		List<String> word_abc = Arrays.asList(new String[] { "a", "b", "c" });
		List<String> word_caa = Arrays.asList(new String[] { "c", "a", "a" });
		List<String> word_cbc = Arrays.asList(new String[] { "c", "b", "c" });

		/*
		 * words that should be in the transformed automaton
		 */
		List<String> word_aa = Arrays.asList(new String[] { "a", "a" });
		List<String> word_ab = Arrays.asList(new String[] { "a", "b" });
		List<String> word_ca = Arrays.asList(new String[] { "c", "a" });


	
		IDawg<String, String> dawg3 = dawgFactoryStringString.getEmptyDawg(signaturePre);
		dawg3 = dawg3.add(word_aaa);
		dawg3 = dawg3.add(word_abb);
		dawg3 = dawg3.add(word_abc);
		dawg3 = dawg3.add(word_caa);
		dawg3 = dawg3.add(word_cbc);

		Dawg<String, String> dawg4 = new ReorderAndRenameDawgBuilder<String, String>(
					dawgFactoryStringString, 
					(Dawg<String, String>) dawg3, 
					"v", 
					"w",
					false,
					true)
				.build();
		
		assertTrue(dawg4.getColnames().equals(signaturePost));
		assertTrue(dawg4.accepts(word_aa));
		assertTrue(dawg4.accepts(word_ab));
		assertTrue(dawg4.accepts(word_ca));
	}
	
	/**
	 * Example for merging two columns
	 *  - moves from right to left
	 *  - source column is in the middle
	 *  - target column is at the very start
	 */
	@Test
	public void test3() {
		DawgFactory<String, String> dawgFactoryStringString = 
				new DawgFactory<String, String>(getEprTheory());
		dawgFactoryStringString.addConstants(getAllConstants());
		
		SortedSet<String> signaturePre = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePre.addAll(Arrays.asList(new String[] { "u", "v", "w"}));
		
		SortedSet<String> signaturePost = new TreeSet<String>(EprHelpers.getColumnNamesComparator());
		signaturePost.addAll(Arrays.asList(new String[] { "u", "w" }));
	

		/*
		 * word in the original automaton
		 */
		List<String> word_aaa = Arrays.asList(new String[] { "a", "a", "a" });
		List<String> word_bba = Arrays.asList(new String[] { "b", "b", "a" });
		List<String> word_abc = Arrays.asList(new String[] { "a", "b", "c" });
		List<String> word_cca = Arrays.asList(new String[] { "c", "c", "a" });
		List<String> word_cbc = Arrays.asList(new String[] { "c", "b", "c" });

		/*
		 * words that should be in the transformed automaton
		 */
		List<String> word_aa = Arrays.asList(new String[] { "a", "a" });
		List<String> word_ba = Arrays.asList(new String[] { "b", "a" });
		List<String> word_ca = Arrays.asList(new String[] { "c", "a" });


	
		IDawg<String, String> dawg3 = dawgFactoryStringString.getEmptyDawg(signaturePre);
		dawg3 = dawg3.add(word_aaa);
		dawg3 = dawg3.add(word_bba);
		dawg3 = dawg3.add(word_abc);
		dawg3 = dawg3.add(word_cca);
		dawg3 = dawg3.add(word_cbc);

		Dawg<String, String> dawg4 = new ReorderAndRenameDawgBuilder<String, String>(
					dawgFactoryStringString, 
					(Dawg<String, String>) dawg3, 
					"v", 
					"u",
					false,
					true)
				.build();
		
		assertTrue(dawg4.getColnames().equals(signaturePost));
		assertTrue(dawg4.accepts(word_aa));
		assertTrue(dawg4.accepts(word_ba));
		assertTrue(dawg4.accepts(word_ca));
	}
	
}
