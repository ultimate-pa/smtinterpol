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

public class ScopeCmd extends Cmd {

	private final String mCmd;
	private int mNumScopes, mLastNumScopes;

	public ScopeCmd(String cmd, int numScopes) {
		mCmd = cmd;
		mNumScopes = numScopes;
	}

	public boolean isScopeStart() {
		return mCmd == "push";
	}

	@Override
	public void dump(PrintWriter writer) {
		writer.print('(');
		writer.print(mCmd);
		writer.print(' ');
		writer.print(mNumScopes);
		writer.println(')');
	}

	public int getNumScopes() {
		return mNumScopes;
	}

	public void tryNumScopes(int numScopes) {
		mLastNumScopes = mNumScopes;
		mNumScopes = numScopes;
	}

	public void reset() {
		mNumScopes = mLastNumScopes;
	}

	@Override
	public String toString() {
		return mCmd.toUpperCase();
	}

}
