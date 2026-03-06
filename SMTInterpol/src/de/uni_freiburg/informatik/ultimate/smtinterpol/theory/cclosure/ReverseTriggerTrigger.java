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

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleList;

/**
 * Trigger that holds two lists: reverse triggers and function applications (on the argument). When merged, both lists
 * are joined and every ReverseTrigger in one list is activated on every function application in the other list (and
 * vice versa).
 *
 * @author Jochen Hoenicke, Jürgen Christ
 */
public final class ReverseTriggerTrigger implements Trigger {

	private final SimpleList<ReverseTrigger> mTriggers = new SimpleList<>();
	private final List<CCAppTerm> mApplications = new ArrayList<>();

	public SimpleList<ReverseTrigger> getTriggers() {
		return mTriggers;
	}

	public List<CCAppTerm> getApplications() {
		return mApplications;
	}

	/**
	 * Add a reverse trigger to the triggers list. The trigger must not be in any list.
	 */
	public void addTrigger(final ReverseTrigger trigger) {
		mTriggers.append(trigger);
	}

	/**
	 * Add a function application to the applications list.
	 */
	public void addApplication(final CCAppTerm app) {
		mApplications.add(app);
	}

	@Override
	public void merge(final CClosure engine, final Trigger other) {
		assert other instanceof ReverseTriggerTrigger;
		final ReverseTriggerTrigger otherRev = (ReverseTriggerTrigger) other;

		// Cross-activate: every trigger in this list on every app in other's list
		for (final ReverseTrigger trigger : mTriggers) {
			for (final CCAppTerm app : otherRev.mApplications) {
				trigger.activate(app, false);
			}
		}
		// Every trigger in other's list on every app in this list
		for (final ReverseTrigger trigger : otherRev.mTriggers) {
			for (final CCAppTerm app : mApplications) {
				trigger.activate(app, false);
			}
		}

		// Join both lists
		mTriggers.joinList(otherRev.mTriggers);
		mApplications.addAll(otherRev.mApplications);
	}
}
