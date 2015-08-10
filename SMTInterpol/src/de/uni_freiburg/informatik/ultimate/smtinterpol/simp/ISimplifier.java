/*
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.simp;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;

/**
 * Basic interface for all simplifiers in this package.  This interface
 * specifies bounded simplifiers.  Every simplifier that implements this
 * interface is allowed to perform a limited number of steps.  The concrete
 * semantics of "step" is left to the individual simplifier and documented
 * there.  If the number of allowed steps is exhausted, the simplifier only
 * copies the remaining term without performing additional simplifications.
 * 
 * The simplifiers also support asynchronous termination.  If an asynchronous
 * termination request is issued, the simplifier immediately stops work and
 * returns its input term.
 * @author Juergen Christ
 */
public interface ISimplifier {

	public Term simplify(Term input);

	/**
	 * Set the upper bound on the number of steps this simplifier is allowed to
	 * perform.  The concrete interpretation of a step is left to the concrete
	 * simplifier.  See the documentation for the concrete simplifier for more
	 * details.  There is no special "unbounded number of steps" marker.  Use
	 * Long.MAX_VALUE if you don't want a reasonable small limit.
	 * @param bound The number of steps allowed by this simplifier.
	 */
	public void setStepBound(long bound);

	/**
	 * Request for asynchronous termination.  This request can be used to
	 * terminate simplification.  If simplification is terminated by this
	 * function before the simplification process is finished, the original
	 * term will be returned from {{@link #simplify(Term)}.
	 * @param terminate The asynchronous termination request.
	 */
	public void setTerminationRequest(TerminationRequest terminate);

	/**
	 * Get the name of this simplifier.
	 * @return Name of this simplifier.
	 */
	public String getName();
}
