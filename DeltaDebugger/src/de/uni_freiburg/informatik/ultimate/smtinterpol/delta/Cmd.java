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

public abstract class Cmd {
	
	private boolean mActive = true;
	
	public void activate() {
		mActive = true;
	}
	
	public void deactivate() {
		mActive = false;
	}
	
	public boolean isActive() {
		return mActive;
	}
	
	public boolean canBeRemoved() { // NOPMD
		return true;
	}
	
	public abstract void dump(PrintWriter writer);
	
	public boolean hasDefinitions() { // NOPMD
		return false;
	}
	
	public void insertDefinitions(Map<String, Cmd> context) { // NOPMD
		// Nothing to do
	}
	
	public void addUsedDefinitions(// NOPMD
			Map<String, Cmd> context, Set<Cmd> usedDefs) {
		// Nothing to do
	}
	
	public String provideFeature() { // NOPMD
		return null;
	}
	
	public void checkFeature(Map<String, Cmd> features) { // NOPMD
		// Nothing to do
	}
	
}
