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
package de.uni_freiburg.informatik.ultimate.smtinterpol.samples;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

public final class InterpolationUsageStub {

	private InterpolationUsageStub() {
		// Hide constructor
	}

	public static void main(String[] args) {
		try {
			final Script s = new SMTInterpol(new DefaultLogger());
			s.setOption(":produce-proofs", true);
			s.setLogic(Logics.QF_LIA);
			s.declareFun("x", new Sort[0], s.sort("Int"));
			s.declareFun("y", new Sort[0], s.sort("Int"));
			s.assertTerm(s.annotate(
					s.term(">",s.term("x"), s.term("y")),
					new Annotation(":named", "phi_1")));
			s.assertTerm(s.annotate(
					s.term("=", s.term("x"), s.numeral("0")),
					new Annotation(":named", "phi_2")));
			s.assertTerm(s.annotate(
					s.term(">", s.term("y"), s.numeral("0")),
					new Annotation(":named", "phi_3")));
			if (s.checkSat() == LBool.UNSAT) {
				Term[] interpolants;
				interpolants = s.getInterpolants(new Term[] {
						s.term("phi_1"),
						s.term("phi_2"),
						s.term("phi_3") });
				System.out.println(interpolants);
				interpolants = s.getInterpolants(new Term[] {
						s.term("phi_2"),
						s.term("and", s.term("phi_1"), s.term("phi_3")) });
				System.err.println(interpolants);
			}
		} catch (final SMTLIBException ex) {
			System.out.println("unknown");
			ex.printStackTrace(System.err);
		}
	}
}
