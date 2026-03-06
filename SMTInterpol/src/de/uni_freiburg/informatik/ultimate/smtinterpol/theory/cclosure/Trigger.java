/*
 * Copyright (C) 2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

/**
 * Interface for trigger objects stored in the global signature-to-trigger map. When two classes are merged and
 * rehashing at checkpoint produces an existing signature, the two triggers are merged. The design allows adding more
 * trigger types later for advanced e-matching.
 *
 * @author Jochen Hoenicke, Jürgen Christ
 */
public interface Trigger {

	/**
	 * Merge this trigger with another. Called when processing the signature todo at checkpoint and the new signature
	 * already has an entry in the map. The engine is needed for side effects (e.g. addPendingCongruence, activating
	 * reverse triggers). The implementation may keep the existing trigger's state and incorporate the other, or create a
	 * new merged trigger; the caller will replace the map entry with the result and keep the previous value for undo.
	 *
	 * @param engine
	 *            the congruence closure engine.
	 * @param other
	 *            the trigger to merge in (from the rehashed signature).
	 */
	void merge(CClosure engine, Trigger other);
}
