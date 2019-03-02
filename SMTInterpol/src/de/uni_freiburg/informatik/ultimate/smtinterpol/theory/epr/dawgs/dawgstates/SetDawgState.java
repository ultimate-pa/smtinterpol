/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates;

import java.util.Set;

public class SetDawgState extends DawgState {

	private final Set<DawgState> mDawgStates;

	public SetDawgState(Set<DawgState> dawgStates, DawgState replacement) {
		super(replacement);
		mDawgStates = dawgStates;
	}

	public Set<DawgState> getInnerStates() {
		return mDawgStates;
	}

	@Override
	public String toString() {
		final StringBuilder innerDawgStateHashCodes = new StringBuilder();
		String comma = "";
		for (DawgState ds : mDawgStates) {
			innerDawgStateHashCodes.append(comma);
			comma = ", ";
			innerDawgStateHashCodes.append(ds.hashCode() % 10000);
		}

		return String.format("SetDawgState%d:%s", this.hashCode() % 10000, innerDawgStateHashCodes);
	}
}