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

import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * This class is the abstract superclass of all proof node converters.
 * 
 * @author Christian Schilling
 */
public class AConverter {
	// appendable
	final Appendable mAppendable;
	// theory
	final Theory mTheory;
	// term converter
	final TermConverter mConverter;
	// computation simplifier
	final ComputationSimplifier mSimplifier;
	
	/* prefixes */
	
	// prefix resolution lemmata use
	protected static final String RESOLUTION_LEMMA_PREFIX = "res";
	
	// prefix LA lemmata use
	protected static final String LA_LEMMA_PREFIX = "la";
	
	// prefix CC sub-lemmata use
	protected static final String CC_LEMMA_PREFIX = "cc";
	
	// prefix some rewrite rules use
	protected static final String REWRITE_PREFIX = "rw";
	
	/**
	 * @param appendable appendable to write the proof to
	 * @param theory the theory
	 * @param converter term converter
	 * @param simplifier computation simplifier
	 */
	protected AConverter(final Appendable appendable, final Theory theory,
			final TermConverter converter,
			final ComputationSimplifier simplifier) {
		mAppendable = appendable;
		mTheory = theory;
		mConverter = converter;
		mSimplifier = simplifier;
	}
	
	/**
	 * This method writes a string to the appendable.
	 * 
	 * @param string string that is written
	 * @throws RuntimeException thrown if an IOException is caught
	 */
	protected void writeString(String string) {
		try {
			mAppendable.append(string);
        } catch (IOException e) {
            throw new RuntimeException("Appender throws IOException", e);
        }
	}
}
