package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LASharedTerm;

public class ClausifierTermInfo {
	// flags for boolean terms
	static final int POS_AXIOMS_ADDED = 1;
	static final int NEG_AXIOMS_ADDED = 2;
	static final int POS_AUX_AXIOMS_ADDED = 4;
	static final int NEG_AUX_AXIOMS_ADDED = 8;
	// flags for all interpreted or boolean terms
	static final int AUX_AXIOM_ADDED = 16;

	private int mFlags;

	private NamedAtom mAtom;
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

	public int getFlags() {
		return mFlags;
	}

	public void setFlags(final int flag) {
		mFlags |= flag;
	}
}
