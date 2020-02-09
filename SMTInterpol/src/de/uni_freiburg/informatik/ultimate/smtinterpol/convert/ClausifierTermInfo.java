package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LASharedTerm;

public class ClausifierTermInfo {
	// flags for boolean terms
	public static final int POS_AXIOMS_ADDED = 1;
	public static final int NEG_AXIOMS_ADDED = 2;
	public static final int POS_AUX_AXIOMS_ADDED = 4;
	public static final int NEG_AUX_AXIOMS_ADDED = 8;
	// flags for all interpreted or boolean terms
	public static final int AUX_AXIOM_ADDED = 16;

	public static final int HAS_CC_TERM = 32;
	public static final int HAS_LA_TERM = 64;
	public static final int HAS_LITERAL = 128;

	private CCTerm mCCTerm;
	private LASharedTerm mLATerm;
	private ILiteral mLiteral;

	public boolean hasCCTerm() {
		return mCCTerm != null;
	}

	public boolean hasLAVar() {
		return mLATerm != null;
	}

	public CCTerm getCCTerm() {
		return mCCTerm;
	}

	public void setCCTerm(final CCTerm ccterm) {
		mCCTerm = ccterm;
	}

	public LASharedTerm getLATerm() {
		return mLATerm;
	}

	public void setLATerm(final LASharedTerm laterm) {
		mLATerm = laterm;
	}

	@Override
	public String toString() {
		return "TermInfo[CC:" + mCCTerm + ",LA:" + mLATerm + "]";
	}
}
