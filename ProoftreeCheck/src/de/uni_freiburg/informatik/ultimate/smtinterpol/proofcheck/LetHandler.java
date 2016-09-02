/*
 * Copyright (C) 2012-2013 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import java.util.HashMap;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * This class is used to abbreviate a lemma in the proof.
 * 
 * As abbreviation a prefix followed by the number assigned by SMTInterpol
 * is written in the Isabelle proof.
 * The string is partly taken from the SMTInterpol term variable name
 * '.cseX', where X is a unique number.
 * 
 * @author Christian Schilling
 */
public class LetHandler {
	// mapping from let variable to represented lemma
	private final HashMap<TermVariable, Term> mLet2Term;
	
	/**
	 * constructor
	 */
	public LetHandler() {
		mLet2Term = new HashMap<TermVariable, Term>();
	}
	
	/**
	 * This method reads the unique part from the term variable name.
	 * It is a number, but is only used as a string.
	 * 
	 * @param variable the term variable
	 * @return the number associated with this variable
	 */
	public String getNumberString(TermVariable variable) {
		final String name = variable.getName();
		assert ((name.startsWith(".cse")) && (name.length() > 4));
		return name.substring(4);
	}
	
	/**
	 * This method returns the lemma given the SMTInterpol abbreviation.
	 * 
	 * @param variable abbreviation used by SMTInterpol
	 * @return the lemma (term and number)
	 */
	public Term getLemma(TermVariable variable) {
		assert (mLet2Term.get(variable) != null);
		return mLet2Term.get(variable);
	}
	
	/**
	 * This method adds a new lemma.
	 * 
	 * @param variable term variable used by SMTInterpol.
	 * @param term abbreviated term
	 */
	public void add(TermVariable variable, Term term) {
		assert (!mLet2Term.containsKey(variable));
		mLet2Term.put(variable, term);
	}
	
	/**
	 * This method clears the map between two subsequent proofs.
	 */
	public void clear() {
		mLet2Term.clear();
	}
	
	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		
		builder.append('{');
		String append = "";
		for (final Entry<TermVariable, Term> entry : mLet2Term.entrySet()) {
			builder.append(append);
			append = ", ";
			builder.append(entry.getKey().toString());

			builder.append(" ~> ");
			builder.append(entry.getValue().toStringDirect());
		}
		builder.append('}');
		
		return builder.toString();
	}
}
