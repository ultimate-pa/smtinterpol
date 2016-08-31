package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;

public class TwoWatcher {

	TwoWatcher mOther;
	
	ClauseLiteral mWatchedLiteral;
	
	DawgFactory<ApplicationTerm, TermVariable> mDawgFactory;
	
	/**
	 * The literals this has watched before, together with the reason why it hat to be reset.
	 */
	Map<ClauseLiteral, DecideStackLiteral> mHistory = new HashMap<ClauseLiteral, DecideStackLiteral>();
	
	public TwoWatcher(ClauseLiteral watchedLiteral, 
			TwoWatcher other, 
			DawgFactory<ApplicationTerm, TermVariable> dawgFactory) {
		mWatchedLiteral = watchedLiteral;
		mOther = other;
		other.mOther = this;
		mDawgFactory = dawgFactory;
	}
	
	public boolean isOneWatcher() {
		return mOther == null;
	}

	public void makeOneWatcher(DecideStackLiteral reason) {
		mHistory.put(mWatchedLiteral, reason);
		mOther = null;
	}
	
	public void reset(ClauseLiteral newWatchedLiteral, DecideStackLiteral reason) {
		assert mWatchedLiteral.conflictsWith(reason);
		mHistory.put(mWatchedLiteral, reason);
		mWatchedLiteral = newWatchedLiteral;
	}
	
	public IDawg<ApplicationTerm, TermVariable> getPoints() {
		return mDawgFactory.createJoinDawg(mHistory, mWatchedLiteral);
	}
}
