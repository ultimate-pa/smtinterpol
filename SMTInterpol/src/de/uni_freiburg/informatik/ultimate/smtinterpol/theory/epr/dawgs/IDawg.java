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

import java.util.List;
import java.util.Map;
import java.util.SortedSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.BinaryRelation;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public interface IDawg<LETTER, COLNAMES> extends Iterable<List<LETTER>> {
	
	SortedSet<COLNAMES> getColNames();
	
//	int getArity();
	
//	public IDawg<LETTER, COLNAMES> join(IDawg<LETTER, COLNAMES> other);

	IDawg<LETTER, COLNAMES> complement();
	
//	public IDawg<LETTER, COLNAMES> union(IDawg<LETTER, COLNAMES> other);
	
	boolean accepts(List<LETTER> word);

	/**
	 * Add one point to this Dawg
	 * Requires:
	 *  - arguments.length equals the arity of this dawg
	 *  - arguments only contains constants
	 * @param arguments
	 */
	IDawg<LETTER, COLNAMES> add(List<LETTER> arguments);

	/**
	 * Add all points of a given Dawg to this Dawg
	 * Requires:
	 *  - dawg's arities must be equal
	 * @param dawg
	 */
//	public void addAll(IDawg<LETTER, COLNAMES> dawg);
	
	/**
	 * Returns a new Dawg that recognizes the union language of this dawg and the
	 * argument Dawg.
	 */
	IDawg<LETTER, COLNAMES> union(IDawg<LETTER, COLNAMES> other);

	boolean isEmpty();

	boolean isUniversal();

	/**
	 * same as join??
	 * @param fp
	 * @return
	 */
	IDawg<LETTER, COLNAMES> intersect(IDawg<LETTER, COLNAMES> other);
	
	IDawg<LETTER, COLNAMES> difference(IDawg<LETTER, COLNAMES> other);

//	public void removeAll(IDawg<LETTER, COLNAMES> other);

	/**
	 * Corresponds to the "superset or equal" set operation.
	 * @param points
	 * @return
	 */
	boolean supSetEq(IDawg<LETTER, COLNAMES> points);

	/**
	 * Return a dawg where only the points are selected that match the given mapping.
	 * The mappings says for some columns what value they must have.
	 * (this is a special version of the normal select operation sigma_phi, where phi has the form x=a, 
	 *  for a column name x and a letter a)
	 *  Note that this does no project operation. The signature of the output dawg is the same as the 
	 *  signature of the input dawg (this Dawg).
	 * 
	 * @param selectMap restricts some COLNAMES in the signature to only one LETTER
	 * @return
	 */
	IDawg<LETTER, COLNAMES> select(Map<COLNAMES, LETTER> selectMap);

	/**
	 * 
	 * @return true iff the language of this dawg contains exactly one element
	 */
	boolean isSingleton();

	/**
	 * 
	 * @param translation Maps colnames of the predicate signature to colnames of the clause signature and constants
	 * @param targetSignature the signature of the clause
	 * @return
	 */
	IDawg<LETTER, COLNAMES> translatePredSigToClauseSig(
			Map<COLNAMES, COLNAMES> translationColnameToColname,
			Map<COLNAMES, LETTER> translationColnameToLetter,
			DawgSignature<COLNAMES> targetSignature);

	/**
	 * There are three main "players" in this operation:
	 *  <li> a Dawg with the signature of a given clause (this)
	 *  <li> a ClauseLiteral with some EprPredicate and some arguments (argList, EprPredicate has been matched elsewhere)
	 *  <li> a DecideStackLiteral over the same EprPredicate as the ClauseLiteral's 
	 *    the resulting Dawg's signature will be that of the DecideStackLiteral (given as newSignature)
	 * 
	 * @param binaryRelation maps colnames of the clause signature to colnames in the  predicate's signature
	 * @param argList the arguments of the ClauseLiteral that has the predicate whose signature we want to translate to
	 * @param newSignature the predicate's signature
	 * @return
	 */
	IDawg<LETTER, COLNAMES> translateClauseSigToPredSig(
			BinaryRelation<COLNAMES, COLNAMES> binaryRelation, List<Object> argList, DawgSignature<COLNAMES> newSignature);
	/**
	 * Lists the language of this dawg word by word
	 * 
	 * Beware: the space complexity of this method is equal to the size of the dawgs language
	 * @return
	 */
	Iterable<List<LETTER>> getAllPointsSorted();

}
