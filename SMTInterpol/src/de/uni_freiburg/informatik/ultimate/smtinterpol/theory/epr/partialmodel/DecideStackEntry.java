/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

/**
 * Parent class for everything that may lie on the epr decide stack.
 * (e.g. different kinds of literals and markers)
 *
 * @author Alexander Nutz
 */
public abstract class DecideStackEntry {

	/**
	 * A number indicating where on the epr decide stack, relatively to other entries,
	 * this entry lies.
	 * Note that these number may not be adjacent for entries that are adjacent on the
	 * epr decide stack, but their sequence is always strictly increasing from the bottom
	 * to the top of the epr decide stack.
	 */
	final int nr;

	public DecideStackEntry(final int i) {
		nr = i;
	}

	abstract void push();

	abstract void pop();
}
