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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

/**
 * This class abstracts from the use of the simplifier for computations.
 * Currently it just returns 'simp'.
 * This can be extended.
 * 
 * @author Christian Schilling
 */
public class ComputationSimplifier {
	/**
	 * This method translates a computation simplification step.
	 * Currently it just returns 'simp'.
	 * 
	 * @return the proof rule string
	 */
	public String getRule() {
		return "simp";
	}
}
