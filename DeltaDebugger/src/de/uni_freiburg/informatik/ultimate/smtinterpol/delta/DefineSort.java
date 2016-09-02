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

import de.uni_freiburg.informatik.ultimate.logic.Sort;

public class DefineSort extends Cmd {
	
	private final String mSort;
	private final Sort[] mParams;
	private final Sort mDefinition;
	
	public DefineSort(String sort, Sort[] params, Sort definition) {
		mSort = sort;
		mParams = params;
		mDefinition = definition;
	}

	@Override
	public void dump(PrintWriter writer) {
		writer.print("(define-sort ");
		writer.print(mSort);
		writer.print(" (");
		String sep = "";
		for (final Sort p : mParams) {
			writer.print(sep);
			writer.print(p.getName());
			sep = " ";
		}
		writer.print(") ");
		writer.print(mDefinition);
		writer.println(')');
	}

	@Override
	public boolean hasDefinitions() {
		return true;
	}
	
	@Override
	public String toString() {
		return "DEFINE_SORT " + mSort;
	}

}
