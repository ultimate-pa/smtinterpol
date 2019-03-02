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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

/**
 * Interface for the commonalities of epr decide stack literals (class DecideStackLiteral)
 * (i.e. decisions internal to the epr theory, described by an epr predicate, a polarity and a dawg)
 * and epr ground literals (class EprGroundLiteral)
 * (i.e. literals over an epr predicate that are ground -- their dawg's language has cardinality 1).
 *
 * @author Alexander Nutz
 */
public interface IEprLiteral {

	public EprPredicate getEprPredicate();

	public boolean getPolarity();

	public IDawg<ApplicationTerm, TermVariable> getDawg();

	/**
	 * To be called before this object is disposed of.
	 * Severs all links to this object that other objects may hold.
	 */
	public void unregister();

	public void registerConcernedClauseLiteral(ClauseEprLiteral cel);
}
