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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents all commands that take one term.  These are
 * - assert
 * - simplify
 * @author Juergen Christ
 */
public class OneTermCmd extends AbstractOneTermCmd {
	
	private final String mCmd;
	
	public OneTermCmd(String cmd, Term term) {
		super(term);
		mCmd = cmd;
	}

	@Override
	public void dump(PrintWriter writer) {
		super.dump(writer);
		writer.print('(');
		writer.print(mCmd);
		writer.print(' ');
		new PrintTerm().append(writer, mTerm);
		writer.println(')');
	}
	
	public String getCmd() {
		return mCmd;
	}
	
	@Override
	public void insertDefinitions(Map<String, Cmd> context) {
		new NamedHelper().addNames(mTerm, context, this);
	}

	@Override
	public void addUsedDefinitions(
			Map<String, Cmd> context, Set<Cmd> usedDefs) {
		if (mPreCmds != null) {
			/* If we have pre commands, we need to add the definitions since the
			 * symbols in the term would otherwise not be well defined.
			 */
			for (Cmd cmd : mPreCmds)
				if (cmd.isActive())
					cmd.insertDefinitions(context);
		}
		new DefinitionTracker(context, usedDefs).track(mTerm);
	}
	
	public String toString() {
		return mCmd.toUpperCase();
	}

}
