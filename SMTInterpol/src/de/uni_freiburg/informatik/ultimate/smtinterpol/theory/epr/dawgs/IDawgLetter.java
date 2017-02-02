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
import java.util.Set;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
interface IDawgLetter<LETTER, COLNAMES> {
	
	
	Set<IDawgLetter<LETTER, COLNAMES>> complement();

	Set<IDawgLetter<LETTER, COLNAMES>> difference(IDawgLetter<LETTER, COLNAMES> other);

	IDawgLetter<LETTER, COLNAMES> intersect(IDawgLetter<LETTER, COLNAMES> other);

	boolean matches(LETTER ltr, List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex);

	IDawgLetter<LETTER, COLNAMES> restrictToLetter(LETTER selectLetter);
}