package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;

public class SimpleTerminationRequest implements TerminationRequest {

	boolean mTerminationRequested;

	public SimpleTerminationRequest() {
		mTerminationRequested = false;
	}

	public void setTerminationRequested(final boolean requested) {
		mTerminationRequested = requested;
	}

	@Override
	public boolean isTerminationRequested() {
		return mTerminationRequested;
	}
}
