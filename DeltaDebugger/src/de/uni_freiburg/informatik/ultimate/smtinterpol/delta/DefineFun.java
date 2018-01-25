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

import java.io.PrintWriter;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class DefineFun extends AbstractOneTermCmd {

	private final String mFun;
	private final TermVariable[] mParams;
	private final Sort mResultSort;

	public DefineFun(final String fun, final TermVariable[] params, final Sort resultSort,
			final Term definition) {
		super(definition);
		mFun = fun;
		mParams = params;
		mResultSort = resultSort;
	}

	@Override
	public void dump(final PrintWriter writer) {
		super.dump(writer);
		writer.print("(define-fun ");
		writer.print(mFun);
		writer.print(" (");
		for (final TermVariable tv : mParams) {
			writer.print('(');
			writer.print(PrintTerm.quoteIdentifier(tv.getName()));
			writer.print(' ');
			writer.print(tv.getSort());
			writer.print(')');
		}
		writer.print(") ");
		writer.print(mResultSort);
		writer.print(' ');
		new PrintTerm().append(writer, mTerm);
		writer.println(')');
	}

	@Override
	public void insertDefinitions(final Map<String, Cmd> context) {
		context.put(mFun, this);
	}

	@Override
	public String toString() {
		return "DEFINE_FUN " + mFun;
	}

	@Override
	public boolean hasDefinitions() {
		return true;
	}

}
