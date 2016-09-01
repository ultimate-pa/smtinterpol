package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;

public class DawgTranslation<COLNAMES> {
	
	
	COLNAMES[] mNewSignature;
	
	Map<COLNAMES, COLNAMES> mTranslation = new HashMap<COLNAMES, COLNAMES>();
	
	public void addPair(COLNAMES pre, COLNAMES post) {
		mTranslation.put(pre, post);
	}
	
	public void setNewSignature(COLNAMES[] newSig) {
		mNewSignature = newSig;
	}
	
	public Map<COLNAMES, COLNAMES> getTranslation() {
		return mTranslation;
	}
	
	public COLNAMES[] getNewSignature() {
		return mNewSignature;
	}

}
