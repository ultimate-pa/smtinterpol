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

public class DawgTestDuplicateColumns {

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
				new DawgFactory<String, String>(getEprTheory(), getAllConstants());
		
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
		
		assertTrue(dawg4.getColnames().equals(signaturePost));
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
				new DawgFactory<String, String>(getEprTheory(), getAllConstants());
		
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
		
		assertTrue(dawg4.getColnames().equals(signaturePost));
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
				new DawgFactory<String, String>(getEprTheory(), getAllConstants());
		
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
		
		assertTrue(dawg4.getColnames().equals(signaturePost));
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
				new DawgFactory<String, String>(getEprTheory(), getAllConstants());

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
		
		assertTrue(dawg4.getColnames().equals(signaturePost));
		assertTrue(dawg4.accepts(word_abb));
		assertTrue(dawg4.accepts(word_baa));
		assertTrue(dawg4.accepts(word_bbb));

	}
}
