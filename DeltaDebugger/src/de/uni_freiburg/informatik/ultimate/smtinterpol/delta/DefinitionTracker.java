/*
 * Copyright (C) 2012-2013 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class DefinitionTracker extends NonRecursive {
	private class Walker extends TermWalker {

		public Walker(final Term term) {
			super(term);
		}

		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			// Does not need definitions
		}

		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			walker.enqueueWalker(new Walker(term.getSubterm()));
		}

		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			final FunctionSymbol fs = term.getFunction();
			if (!fs.isIntern()) {
				track(fs.getName());
			}
			for (final Term p : term.getParameters()) {
				walker.enqueueWalker(new Walker(p));
			}
		}

		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			for (final Term bound : term.getValues()) {
				walker.enqueueWalker(new Walker(bound));
			}
			walker.enqueueWalker(new Walker(term.getSubTerm()));
		}

		@Override
		public void walk(final NonRecursive walker, final LambdaTerm term) {
			walker.enqueueWalker(new Walker(term.getSubterm()));
		}

		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			walker.enqueueWalker(new Walker(term.getSubformula()));
		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			// Does not need definitions
		}

		@Override
		public void walk(final NonRecursive walker, final MatchTerm term) {
			walker.enqueueWalker(new Walker(term.getDataTerm()));
			for (final Term caseTerm : term.getCases()) {
				walker.enqueueWalker(new Walker(caseTerm));
			}
		}
	}

	private final Map<String, Cmd> mCtx;
	private final Set<Cmd> mUsed;

	public DefinitionTracker(final Map<String, Cmd> ctx, final Set<Cmd> used) {
		mCtx = ctx;
		mUsed = used;
	}

	public void track(final Term t) {
		run(new Walker(t));
	}

	private void track(final String fun) {
		final Cmd definition = mCtx.get(fun);
		if (definition == null) {
			throw new InternalError("No definition found for " + fun);
		}
		mUsed.add(definition);
	}
}
