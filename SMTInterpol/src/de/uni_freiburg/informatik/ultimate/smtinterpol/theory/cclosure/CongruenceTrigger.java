/*
 * Copyright (C) 2009-2026 University of Freiburg
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
 * Trigger that holds a single CCAppTerm for congruence propagation. When merged with another CongruenceTrigger (same
 * signature after rehash), the equality between the two applications is propagated via
 * {@link CClosure#addPendingCongruence}; the existing trigger's application is kept (not the incoming one).
 *
 * @author Jochen Hoenicke, Jürgen Christ
 */
public final class CongruenceTrigger implements Trigger {

	private CCAppTerm mApp;

	/**
	 * Create a congruence trigger with one application term.
	 *
	 * @param app
	 *            the (kept) application term for this signature.
	 */
	public CongruenceTrigger(final CCAppTerm app) {
		mApp = app;
	}

	public CCAppTerm getApp() {
		return mApp;
	}

	@Override
	public void merge(final CClosure engine, final Trigger other) {
		assert other instanceof CongruenceTrigger;
		final CongruenceTrigger otherCong = (CongruenceTrigger) other;
		engine.addPendingCongruence(mApp, otherCong.mApp);
		// Keep the existing app (this.mApp); no change to mApp.
	}
}
