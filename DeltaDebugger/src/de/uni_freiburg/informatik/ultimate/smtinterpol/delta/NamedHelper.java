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

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive.TermWalker;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class NamedHelper {
	
	private final class NamedCollector extends TermWalker {
		public NamedCollector(Term term) {
			super(term);
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			// Cannot contain names
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			for (final Annotation annot : term.getAnnotations()) {
				if (annot.getKey().equals(":named")) {
					mNames.put(annot.getValue().toString(), mCmd);
				}
			}
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			for (final Term t : term.getParameters()) {
				walker.enqueueWalker(new NamedDetector(t));
			}
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			for (final Term t : term.getValues()) {
				walker.enqueueWalker(new NamedDetector(t));
			}
			walker.enqueueWalker(new NamedDetector(term.getSubTerm()));
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(new NamedDetector(term.getSubformula()));
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			// Cannot contain names
		}
	}
	
	private final class NamedDetector extends TermWalker {

		public NamedDetector(Term term) {
			super(term);
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			// Cannot contain names
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			for (final Annotation annot : term.getAnnotations()) {
				if (annot.getKey().equals(":named")) {
					mHasNames = true;
				}
			}
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			for (final Term t : term.getParameters()) {
				walker.enqueueWalker(new NamedDetector(t));
			}
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			for (final Term t : term.getValues()) {
				walker.enqueueWalker(new NamedDetector(t));
			}
			walker.enqueueWalker(new NamedDetector(term.getSubTerm()));
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(new NamedDetector(term.getSubformula()));
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			// Cannot contain names
		}
		
	}
	
	private boolean mHasNames;
	private Map<String, Cmd> mNames;
	private Cmd mCmd;
	
	public boolean checkTerm(Term t) {
		mHasNames = false;
		new NonRecursive().run(new NamedDetector(t));
		return mHasNames;
	}
	
	public void addNames(Term t, Map<String, Cmd> context, Cmd cmd) {
		mNames = context;
		mCmd = cmd;
		new NonRecursive().run(new NamedCollector(t));
	}
}
