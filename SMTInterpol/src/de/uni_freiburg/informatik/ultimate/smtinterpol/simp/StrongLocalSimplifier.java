/*
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.simp;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A strong simplifier that does not use a global context, but only a local
 * context.  A local context is given by the current vertex in the term DAG.
 * Hence, this context simplifier considers linearly many (in the DAG size of
 * the input formula) different context.  For every of these contexts, it checks
 * if one of the arguments can be omitted.  One such a check is considered a
 * step by this simplifier.
 * @author Juergen Christ
 */
public class StrongLocalSimplifier extends AbstractSimplifier {

	private final Script mScript;

	public StrongLocalSimplifier(Script script, Logger logger) {
		super(logger);
		mScript = script;
	}
	@Override
	public String getName() {
		return "StrongLocal";
	}

	@Override
	protected Term dosimplify(Term input) {
		FormulaUnLet unlet = new FormulaUnLet();
		Term unletinput = unlet.unlet(input);
		return transform(unletinput);
	}

	private final boolean isConsidered(Term t) {
		if (t.getSort() == t.getTheory().getBooleanSort()
				&& t instanceof ApplicationTerm) {
			// We need at least two arguments to remove one...
			return ((ApplicationTerm) t).getParameters().length > 1;
		}
		return false;
	}
	@Override
	protected void convert(Term t) {
		isAsyncTermination();
		if (isConsidered(t) && nextStep()) {
			ApplicationTerm at = (ApplicationTerm) t;
			// TODO: implement
		}
		super.convert(t);
	}

}
