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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public abstract class AbstractOneTermCmd extends TermCmd {

	protected Term mTerm;
	private Term mOldTerm;
	protected List<Cmd> mPreCmds;
	
	protected AbstractOneTermCmd(Term term) {
		mTerm = term;
		addTerm(term);
	}
	
	public Term getTerm() {
		return mTerm;
	}
	
	public void setTerm(Term newTerm) {
		mOldTerm = mTerm;
		mTerm = newTerm;
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

}
