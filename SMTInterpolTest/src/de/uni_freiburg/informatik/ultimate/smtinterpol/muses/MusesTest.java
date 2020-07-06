package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * Tests for everything that has to do with MUSes.
 *
 * @author LeonardFichtner
 *
 */
public class MusesTest {

	private Script setupScript(final Logics logic) {
		final Script script = new SMTInterpol();
		script.setOption(":produce-models", true);
		script.setOption(":produce-proofs", true);
		script.setOption(":interactive-mode", true);
		script.setOption(":produce-unsat-cores", true);
		script.setLogic(logic);
		return script;
	}

	private void setupSatSet(final Script script, final CritAdministrationSolver solver) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 5; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term z = script.term("z");
		final Term c0 = script.term(">=", x, script.numeral("30"));
		final Term c1 = script.term(">=", x, script.numeral("101"));
		final Term c2 = script.term("<", x, z);
		final Term c3 = script.term("<=", z, script.numeral("101"));
		final Term c4 = script.term("=", y, script.numeral("2"));
		solver.declareConstraint(c0, annots.get(0));
		solver.declareConstraint(c1, annots.get(1));
		solver.declareConstraint(c2, annots.get(2));
		solver.declareConstraint(c3, annots.get(3));
		solver.declareConstraint(c4, annots.get(4));
	}

	private void setupUnsatSet(final Script script, final CritAdministrationSolver solver) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 10; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term z = script.term("z");
		final Term c0 = script.term("=", x, script.numeral("53"));
		final Term c1 = script.term(">", x, script.numeral("23"));
		final Term c2 = script.term("<", x, z);
		final Term c3 = script.term("=", x, script.numeral("535"));
		final Term c4 = script.term("=", y, script.numeral("1234"));
		final Term c5 = script.term("<=", z, script.numeral("23"));
		final Term c6 = script.term(">=", x, script.numeral("34"));
		final Term c7 = script.term("=", y, script.numeral("4321"));
		final Term c8 = script.term("=", x, script.numeral("23"));
		final Term c9 = script.term("=", x, script.numeral("5353"));
		solver.declareConstraint(c0, annots.get(0));
		solver.declareConstraint(c1, annots.get(1));
		solver.declareConstraint(c2, annots.get(2));
		solver.declareConstraint(c3, annots.get(3));
		solver.declareConstraint(c4, annots.get(4));
		solver.declareConstraint(c5, annots.get(5));
		solver.declareConstraint(c6, annots.get(6));
		solver.declareConstraint(c7, annots.get(7));
		solver.declareConstraint(c8, annots.get(8));
		solver.declareConstraint(c9, annots.get(9));
	}

	@Test
	public void testShrinker1() {
		final Script script = setupScript(Logics.ALL);
		final CritAdministrationSolver solver = new CritAdministrationSolver(script);
		setupUnsatSet(script, solver);
		solver.assertCriticalConstraint(4);
		final BitSet workingSet = new BitSet();
		workingSet.flip(0, 10);
		final MusContainer container = ShrinkMethods.shrinkWithoutMap(solver, workingSet);
		Assert.assertFalse(container.getMus().get(0));
		Assert.assertFalse(container.getMus().get(1));
		Assert.assertFalse(container.getMus().get(2));
		Assert.assertFalse(container.getMus().get(3));
		Assert.assertTrue(container.getMus().get(4));
		Assert.assertFalse(container.getMus().get(5));
		Assert.assertFalse(container.getMus().get(6));
		Assert.assertTrue(container.getMus().get(7));
		Assert.assertFalse(container.getMus().get(8));
		Assert.assertFalse(container.getMus().get(9));
	}

	@Test
	public void testShrinker2() {
		final Script script = setupScript(Logics.ALL);
		final CritAdministrationSolver solver = new CritAdministrationSolver(script);
		setupUnsatSet(script, solver);
		solver.assertCriticalConstraint(8);
		final BitSet workingSet = new BitSet();
		workingSet.set(0);
		workingSet.set(3);
		workingSet.set(9);
		workingSet.flip(0, 10);
		final MusContainer container = ShrinkMethods.shrinkWithoutMap(solver, workingSet);
		Assert.assertFalse(container.getMus().get(0));
		Assert.assertFalse(container.getMus().get(1));
		Assert.assertTrue(container.getMus().get(2));
		Assert.assertFalse(container.getMus().get(3));
		Assert.assertFalse(container.getMus().get(4));
		Assert.assertTrue(container.getMus().get(5));
		Assert.assertFalse(container.getMus().get(6));
		Assert.assertFalse(container.getMus().get(7));
		Assert.assertTrue(container.getMus().get(8));
		Assert.assertFalse(container.getMus().get(9));
	}

	@Test
	public void testExtensionLightDemand() {
		final Script script = setupScript(Logics.ALL);
		final CritAdministrationSolver solver = new CritAdministrationSolver(script);
		setupSatSet(script, solver);
		solver.assertUnknownConstraint(1);
		Assert.assertEquals(LBool.SAT, solver.checkSat());
		final BitSet extension = solver.getSatExtension();
		System.out.println(extension.toString());
		Assert.assertTrue(extension.get(0));
		/*
		 * Weird, I don't know why some things are evaluated to true and some to false, but hey it seems to work
		 */
	}

	@Test
	public void testExtensionMediumDemand() {
		final Script script = setupScript(Logics.ALL);
		final CritAdministrationSolver solver = new CritAdministrationSolver(script);
		setupSatSet(script, solver);
		Assert.assertEquals(LBool.SAT, solver.checkSat());
		final BitSet extension = solver.getSatExtensionMoreDemanding();
		System.out.println(extension.toString());
		Assert.assertTrue(extension.get(0));
		Assert.assertTrue(extension.get(1));
		Assert.assertTrue(extension.get(2));
		Assert.assertFalse(extension.get(3));
		Assert.assertFalse(extension.get(4));
	}

	@Test
	public void testExtensionHeavyDemand() {
		final Script script = setupScript(Logics.ALL);
		final CritAdministrationSolver solver = new CritAdministrationSolver(script);
		setupSatSet(script, solver);
		Assert.assertEquals(LBool.SAT, solver.checkSat());
		final BitSet extension = solver.getSatExtensionMaximalDemanding();
		System.out.println(extension.toString());
		Assert.assertTrue(extension.get(0));
		Assert.assertTrue(extension.get(1));
		Assert.assertTrue(extension.get(2));
		Assert.assertFalse(extension.get(3));
		Assert.assertTrue(extension.get(4));
	}
}
