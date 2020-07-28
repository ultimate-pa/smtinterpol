package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;

public class TimeoutHandler implements TerminationRequest {

	TerminationRequest mStackedTermination;
	long mTimeoutStamp;
	boolean mTimeoutIsSet;

	public TimeoutHandler(final TerminationRequest stacked) {
		mStackedTermination = stacked;
		clearTimeout();
	}

	public void clearTimeout() {
		mTimeoutStamp = Long.MAX_VALUE;
		mTimeoutIsSet = false;
	}

	public void setTimeout(final long millis) {
		mTimeoutStamp = System.currentTimeMillis() + millis;
		mTimeoutIsSet = true;
	}

	public boolean timeoutIsSet() {
		return mTimeoutIsSet;
	}

	@Override
	public boolean isTerminationRequested() {
		if (mStackedTermination != null && mStackedTermination.isTerminationRequested()) {
			return true;
		}
		return System.currentTimeMillis() >= mTimeoutStamp;
	}
}
