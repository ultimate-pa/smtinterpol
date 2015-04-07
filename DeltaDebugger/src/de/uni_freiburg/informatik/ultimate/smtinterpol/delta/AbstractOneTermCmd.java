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
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.FormulaLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public abstract class AbstractOneTermCmd extends TermCmd {

	protected Term mTerm;
	private Term mOldTerm;
	protected List<Cmd> mPreCmds;
	
	protected AbstractOneTermCmd(Term term) {
		mTerm = term;
		addTerm(term);
	}
	
	public Term getTerm(boolean unlet) {
		return unlet ? new FormulaUnLet().unlet(mTerm) : mTerm;
	}
	
	public void setTerm(Term newTerm, boolean relet) {
		assert (newTerm != mTerm) : "No change in the term";
		mOldTerm = mTerm;
		mTerm = new FormulaLet().let(newTerm);
	}
	
	public void success() {
		mOldTerm = null;
	}
	
	public void failure() {
		mTerm = mOldTerm;
	}

	public void appendPreCmds(List<Cmd> pres) {
		if (pres == null || pres.isEmpty())
			return;
		if (mPreCmds == null)
			mPreCmds = pres;
		else
			mPreCmds.addAll(pres);
	}
	
	public void removePreCmds(List<Cmd> pres) {
		if (pres == null || pres.isEmpty())
			return;
		mPreCmds.removeAll(pres);
		if (mPreCmds.isEmpty())
			mPreCmds = null;
	}

	@Override
	public void dump(PrintWriter writer) {
		if (mPreCmds != null)
			for (Cmd cmd : mPreCmds)
				if (cmd.isActive())
					cmd.dump(writer);
	}

	public List<Cmd> getPreCmds() {
		List<Cmd> empty = Collections.emptyList();
		return mPreCmds == null ? empty : mPreCmds;
	}

	@Override
	public void addUsedDefinitions(Map<String, Cmd> context, Set<Cmd> usedDefs) {
		new DefinitionTracker(context, usedDefs).track(mTerm);
	}

}
