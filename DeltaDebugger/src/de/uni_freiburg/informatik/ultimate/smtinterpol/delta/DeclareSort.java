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

public class DeclareSort extends Cmd {
	
	private final String mSort;
	private final int mArity;

	public DeclareSort(String sort, int arity) {
		mSort = sort;
		mArity = arity;
	}
	
	@Override
	public void dump(PrintWriter writer) {
		writer.print("(declare-sort ");
		writer.print(mSort);
		writer.print(' ');
		writer.print(mArity);
		writer.println(')');
	}

	@Override
	public boolean canBeRemoved() {
		return true;
	}

	@Override
	public boolean hasDefinitions() {
		return true;
	}
	
	@Override
	public String toString() {
		return "DECLARE_SORT " + mSort;
	}

}
