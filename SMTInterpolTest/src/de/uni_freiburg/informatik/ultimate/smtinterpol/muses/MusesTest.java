package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
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

	private void setupSimpleUnsatSet(final CritAdministrationSolver solver) {

	}

	private void setupMediumUnsatSet(final CritAdministrationSolver solver) {

	}

	private void setupHeavyUnsatSet(final CritAdministrationSolver solver) {

	}

	private void setupSatSet(final Script script, final CritAdministrationSolver solver) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 1; i < 6; i++) {
			names.add("c"+ String.valueOf(i));
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
		final Term c1 = script.term(">=", x, script.numeral("30"));
		final Term c2 = script.term(">=", x, script.numeral("101"));
		final Term c3 = script.term("<", x, z);
		final Term c4 = script.term("<=", z, script.numeral("101"));
		final Term c5 = script.term("=", y, script.numeral("2"));
		solver.declareConstraint(c1, annots.get(0));
		solver.declareConstraint(c2, annots.get(1));
		solver.declareConstraint(c3, annots.get(2));
		solver.declareConstraint(c4, annots.get(3));
		solver.declareConstraint(c5, annots.get(4));
	}

	@Test
	public void testExtensionLightDemand() {
		final Script script = setupScript(Logics.ALL);
		final CritAdministrationSolver solver = new CritAdministrationSolver(script);
		setupSatSet(script, solver);
		solver.assertUnknownConstraint(2);
		solver.assertUnknownConstraint(5);
		final BitSet extension = solver.getSatExtension();
		System.out.println(extension.toString());
		Assert.assertTrue(extension.get(2));
		Assert.assertTrue(extension.get(5));
	}

	public void testExtensionMediumDemand() {

	}

	public void testExtensionHeavyDemand() {

	}
}
