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
 * Represents all commands that take a list of terms.  These are:
 * - get-value
 * - check-allsat
 * @author Juergen Christ
 */
public class TermListCmd extends TermCmd {
	
	private final String mCmd;
	private Term[] mList, mOldList;
	
	public TermListCmd(String cmd, Term[] list) {
		mCmd = cmd;
		mList = list;
		addTerms(list);
	}

	@Override
	public void dump(PrintWriter writer) {
		writer.print('(');
		writer.print(mCmd);
		writer.print(" (");
		PrintTerm pt = new PrintTerm();
		String sep = "";
		for (Term t : mList) {
			writer.print(sep);
			pt.append(writer, t);
			sep = " ";
		}
		writer.println("))");
	}


	@Override
	public void insertDefinitions(Map<String, Cmd> context) {
		NamedHelper nh = new NamedHelper();
		for (Term t : mList)
			nh.addNames(t, context, this);
	}

	@Override
	public void addUsedDefinitions(
			Map<String, Cmd> context, Set<Cmd> usedDefs) {
		DefinitionTracker dt = new DefinitionTracker(context, usedDefs);
		for (Term t : mList)
			dt.track(t);
	}

	public Term[] getTerms() {
		return mList;
	}
	
	public void setNewTerms(Term[] newTerms) {
		mOldList = mList;
		mList = newTerms;
	}
	
	public void failure() {
		mList = mOldList;
	}
	
	public void success() {
		mOldList = null;
	}
	
	public String toString() {
		return mCmd.toUpperCase();
	}

	@Override
	public void checkFeature(Map<String, Cmd> features) {
		if (mCmd.equals("get-value"))
			features.remove(":produce-models");
	}

}
