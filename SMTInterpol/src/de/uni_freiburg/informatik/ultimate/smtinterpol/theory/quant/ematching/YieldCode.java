/*
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.ematching;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantLiteral;

/**
 * Code to add a new interesting substitution for a given literal, including the corresponding CCTerms.
 * 
 * @author Tanja Schindler
 */
public class YieldCode implements ICode {

	private final EMatching mEMatching;
	private final QuantLiteral mQuantLiteral;
	private final Map<Term, Integer> mCandPos;
	private final Map<TermVariable, Integer> mVarPos;

	public YieldCode(final EMatching eMatching, final QuantLiteral qLit, final Map<Term, Integer> candPos,
			final Map<TermVariable, Integer> varPos) {
		mEMatching = eMatching;
		mQuantLiteral = qLit;
		mCandPos = candPos;
		mVarPos = varPos;
	}

	@Override
	public void execute(CCTerm[] register) {
		final Map<Term, CCTerm> cands = new HashMap<>();
		final Map<Term, CCTerm> interestingSubs = new HashMap<>();
		for (final Entry<Term, Integer> candPos : mCandPos.entrySet()) {
			cands.put(candPos.getKey(), register[candPos.getValue()]);
		}
		for (final Entry<TermVariable, Integer> varPos : mVarPos.entrySet()) {
			interestingSubs.put(varPos.getKey(), register[varPos.getValue()]);
		}
		mEMatching.addInterestingSubstitution(mQuantLiteral, interestingSubs, cands);
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("yield(" + mQuantLiteral);
		for (final TermVariable var : mVarPos.keySet()) {
			sb.append(", " + var);
		}
		sb.append(")");
		return sb.toString();
	}

}
