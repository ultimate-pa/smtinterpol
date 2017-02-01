/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.HashMap;
import java.util.Map;

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
