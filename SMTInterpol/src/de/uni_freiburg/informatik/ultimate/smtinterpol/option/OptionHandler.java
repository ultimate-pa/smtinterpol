/*
 * Copyright (C) 2014 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.option;

import java.math.BigInteger;

/**
 * A manager for a set of options.  The functions have an additional parameter
 * that is given to the option map when registering the option.  It can be used
 * to speed up case constructs.  The option map does not enforce any
 * restrictions on this parameter.  Hence, an implementer is free to ignore
 * this parameter.
 * @author Juergen Christ
 */
public interface OptionHandler {
	public void setBooleanOption(String option, boolean value, int userData);
	public void setStringOption(String option, String value, int userData);
	public void setNumeralOption(String option, BigInteger value, int userData);
	
	public boolean getBooleanOption(String option, int userData);
	public String getStringOption(String option, int userData);
	public BigInteger getNumeralOption(String option, int userData);
}
