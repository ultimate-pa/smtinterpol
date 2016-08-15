package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;

public class ClauseQuantifiedLiteral extends ClauseLiteral {

	boolean polarity;
	EprQuantifiedPredicateAtom atom;
	
	HashMap<Integer, HashMap<ClauseQuantifiedLiteral, HashSet<Integer>>> identicalVariablePositionsInOtherClauseLiterals = 
			new HashMap<Integer, HashMap<ClauseQuantifiedLiteral,HashSet<Integer>>>();
	
}
