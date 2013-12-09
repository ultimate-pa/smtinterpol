/*
 * Copyright (C) 2009-2012 University of Freiburg
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
/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Foobar.  If not, see <http://www.gnu.org/licenses/>.
 */
/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Foobar.  If not, see <http://www.gnu.org/licenses/>.
 */
/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Foobar.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.demo;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * A small demo file used to present SMTInterpol in SPIN 2012.
 * 
 * It basically executes the following script:
 * <pre>
 * (set-option :produce-proofs true)
 * (set-logic QF_UFLIA)
 * (declare-fun x () Int)
 * (declare-fun y () Int)
 * (declare-fun z () Int)
 * (declare-fun f (Int) Int)
 * (assert (! (and (= (* 2 x) y) (= (f x) 1)) :named a1))
 * (assert (! (and (= (* 2 z) y) (= (f z) 0)) :named a2))
 * (check-sat)
 * (get-interpolants a1 a2)
 * (exit)
 * </pre>
 * @author Juergen Christ
 */
public final class Spin2012 {
	private Spin2012() {
		// Hide constructor
	}
	public static void main(String[] args) {
		SMTInterpol script = new SMTInterpol(Logger.getRootLogger(), true);
		script.setOption(":produce-proofs", true);
		script.setLogic(Logics.QF_UFLIA);
		script.declareFun("x", new Sort[0], script.sort("Int"));
		script.declareFun("y", new Sort[0], script.sort("Int"));
		script.declareFun("z", new Sort[0], script.sort("Int"));
		script.declareFun("f", new Sort[] {script.sort("Int")},
				script.sort("Int"));
		script.assertTerm(script.annotate(
			script.term("and",
				script.term("=",
					script.term("*", script.numeral("2"), script.term("x")),
					script.term("y")),
				script.term("=",
					script.term("f", script.term("x")),
					script.numeral("1"))),
			new Annotation(":named", "a1")));
		script.assertTerm(script.annotate(
				script.term("and",
					script.term("=",
						script.term("*", script.numeral("2"), script.term("z")),
						script.term("y")),
					script.term("=",
						script.term("f", script.term("z")),
						script.numeral("0"))),
				new Annotation(":named", "a2")));
		LBool isSat = script.checkSat();
		if (isSat == LBool.UNSAT) {
			Term[] interpolants = script.getInterpolants(
					new Term[] {script.term("a1"), script.term("a2")});
			for (int i = 0; i < interpolants.length; ++i) {
				System.out.println("Interpolant " + i + ": "
						+ interpolants[i].toStringDirect());
			}
		} else
			System.out.println("This should not happen!!!");
		script.exit();
	}
}
