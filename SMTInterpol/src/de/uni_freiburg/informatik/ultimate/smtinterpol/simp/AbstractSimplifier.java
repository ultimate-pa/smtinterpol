/*
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.simp;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;

public abstract class AbstractSimplifier extends TermTransformer implements ISimplifier {

	private final static class AsyncTermination extends RuntimeException {
		private static final long serialVersionUID = -704336279965990917L;
	}
	private long mMaxNumSteps;
	private long mNumSteps;
	private final Logger mLogger;
	private TerminationRequest mTerminate;

	public AbstractSimplifier(Logger logger) {
		mMaxNumSteps = Long.MAX_VALUE;
		mLogger = logger;
	}
	@Override
	public final Term simplify(Term input) {
		mNumSteps = 0;
		if (mLogger.isDebugEnabled())
			mLogger.debug("Starting simplifier " + getName()
					+ " with max steps " + mMaxNumSteps);
		Term res = input;
		try {
			res = dosimplify(input);
		} catch (AsyncTermination ignored) {
			mLogger.debug("Simplifier cancelled");
			reset();
		}
		if (mLogger.isDebugEnabled())
			mLogger.debug("Ended simplifier " + getName()
					+ " after " + mNumSteps + "/" + mMaxNumSteps + " steps");
		return res;
	}
	@Override
	public final void setStepBound(long bound) {
		mMaxNumSteps = bound;
	}

	@Override
	public final void setTerminationRequest(TerminationRequest terminate) {
		mTerminate = terminate;
	}

	protected abstract Term dosimplify(Term input);
	protected void isAsyncTermination() {
		if (mTerminate != null && mTerminate.isTerminationRequested())
			throw new AsyncTermination();
	}
	protected boolean nextStep() {
		// Saturate here to prevent wrap around in rare cases.
		if (mNumSteps < mMaxNumSteps)
			++mNumSteps;
		return mNumSteps < mMaxNumSteps;
	}

}
