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

/**
 * Represents all commands that do not take any arguments.  These are:
 * - check-sat
 * - get-assertions
 * - get-proof
 * - get-unsat-core
 * - get-model
 * - get-assignment
 * - exit
 * @author Juergen Christ
 */
public class SimpleCmd extends Cmd {

	private final String mCmd;

	public SimpleCmd(String cmd) {
		mCmd = cmd;
	}

	@Override
	public void dump(PrintWriter writer) {
		writer.print('(');
		writer.print(mCmd);
		writer.println(')');
	}

	@Override
	public String toString() {
		return mCmd.toUpperCase();
	}

	@Override
	public void checkFeature(Map<String, Cmd> features) {
		if (mCmd.equals("get-assertions")) {
			features.remove(":interactive-mode");
		} else if (mCmd.equals("get-proof")) {
			features.remove(":produce-proofs");
		} else if (mCmd.equals("get-model")) {
			features.remove(":produce-models");
		} else if (mCmd.equals("get-unsat-core")) {
			features.remove(":produce-unsat-cores");
		} else if (mCmd.equals(":get-assignment")) {
			features.remove(":produce-assignments");
		}
	}

}
