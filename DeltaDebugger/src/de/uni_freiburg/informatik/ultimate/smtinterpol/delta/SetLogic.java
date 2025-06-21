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

import de.uni_freiburg.informatik.ultimate.logic.Logics;

public class SetLogic extends Cmd {

	private final Logics mLogic;

	public SetLogic(Logics logic) {
		mLogic = logic;
	}

	@Override
	public void dump(PrintWriter writer) {
		writer.print("(set-logic ");
		writer.print(mLogic.getName());
		writer.println(')');
	}

	@Override
	public boolean canBeRemoved() {
		// Never remove set-logic!!!
		return false;
	}

	@Override
	public String toString() {
		return "SET_LOGIC";
	}

}
