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

import de.uni_freiburg.informatik.ultimate.logic.Identifier;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

public class DeclareFun extends Cmd {

	private final String mFun;
	private final Sort[] mParams;
	private final Sort mResultSort;
	
	public DeclareFun(String fun, Sort[] params, Sort resultSort) {
		mFun = fun;
		mParams = params;
		mResultSort = resultSort;
	}
	
	@Override
	public void dump(PrintWriter writer) {
		writer.print("(declare-fun ");
		writer.print(Identifier.quoteIdentifier(mFun));
		writer.print(" (");
		String sep = "";
		for (Sort p : mParams) {
			writer.print(sep);
			writer.print(p);
			sep = " ";
		}
		writer.print(") ");
		writer.print(mResultSort);
		writer.println(')');
	}

	@Override
	public boolean hasDefinitions() {
		return true;
	}

	@Override
	public void insertDefinitions(Map<String, Cmd> context) {
		context.put(mFun, this);
	}
	
	public String toString() {
		return "DECLARE_FUN " + mFun;
	}
	
}
