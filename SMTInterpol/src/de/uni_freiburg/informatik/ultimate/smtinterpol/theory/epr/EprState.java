package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

public class EprState {
	

	/**
	 * Represents a partial model for the parts of the EprTheory 
	 * (EprClause, set EprAtoms, EprPredicate models).
	 * 
	 * Is used to track the different parts of a model that correspond to each 
	 * decide state in the DPLLEngine (e.g. a setLiteral may trigger the introduction of 
	 * new EprClauses..)
	 */
	public EprState() {
		// TODO Auto-generated constructor stub
	}

	
	ArrayList<EprClause> mDerivedClauses;

	ArrayList<Literal> mSetLiterals;
	

}
