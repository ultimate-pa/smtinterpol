package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode;

public class EprClause extends Clause {
	
	Literal[] eprEqualityLiterals;
	Literal[] eprPredicateLiterals;
	Literal[] nonEprLiterals;

	public EprClause(Literal[] literals) {
		super(literals);
		sortEprLiterals(literals);
	}

	public EprClause(Literal[] literals, ProofNode proof) {
		super(literals, proof);
		sortEprLiterals(literals);
	}

	public EprClause(Literal[] literals, int stacklevel) {
		super(literals, stacklevel);
		sortEprLiterals(literals);
	}

	public EprClause(Literal[] literals, ResolutionNode proof, int stacklevel) {
		super(literals, proof, stacklevel);
		sortEprLiterals(literals);
	}

	private void sortEprLiterals(Literal[] literals) {
		int noEqualities = 0;
		int noPredicates = 0;
		int noOthers = 0;
		//TODO: is this (counting then making arrays) more efficient than using a list?
		for (Literal l : literals) {
			if (l.getAtom() instanceof EprEqualityAtom) {
				//TODO: this assert is probably too strict: we have to allow disequalities between quantified variables, right?
				assert l.getSign() == 1 : "Destructive equality reasoning should have eliminated this literal.";
				noEqualities++;
			} else if (l.getAtom() instanceof EprPredicateAtom) {
				noPredicates++;
			} else {
				noOthers++;
			}
		}
		
		eprEqualityLiterals = new Literal[noEqualities];
		eprPredicateLiterals = new Literal[noPredicates];
		nonEprLiterals = new Literal[noOthers];

		//TODO: reusing the counter as array index may be unnecessarily confusing..
		for (Literal l : literals) {
			if (l.getAtom() instanceof EprEqualityAtom) {
				eprEqualityLiterals[--noEqualities] = l;
			} else if (l.getAtom() instanceof EprPredicateAtom) {
				eprPredicateLiterals[--noPredicates] = l;
			} else {
				nonEprLiterals[--noOthers] = l;
			}
		}
	}
	
	/**
	 * Checks if this clause is fulfilled in the current decide state wrt. the EPR theory.
	 * @return null if this clause is fulfilled, a conflict clause otherwise
	 */
	public Clause check() {
		ApplicationTerm[] exceptedConstants = null;
		for (Literal l : eprEqualityLiterals) {
			//TODO fill exceptedConstants, using the "x = c"-type literals
			// probably do this somewhere else, i.e., once per clause
		}
		
		boolean result = false;
		
		for (Literal l : eprPredicateLiterals) {
			EprPredicateAtom e = (EprPredicateAtom) l.getAtom();
			result |= e.getPredicate().check(l.getSign() == 1, exceptedConstants);
		}

		return null; 
	}
}
