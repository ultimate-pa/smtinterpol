package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAnnotation.RuleKind;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

public class DataTypeLemma {

	private final RuleKind mRule;
	private final SymmetricPair<CCTerm>[] mReason;

	public DataTypeLemma(final RuleKind rule, final SymmetricPair<CCTerm>[] reason) {
		mRule = rule;
		mReason = reason;
	}

	public RuleKind getRule() {
		return mRule;
	}

	public SymmetricPair<CCTerm>[] getReason() {
		return mReason;
	}
}
