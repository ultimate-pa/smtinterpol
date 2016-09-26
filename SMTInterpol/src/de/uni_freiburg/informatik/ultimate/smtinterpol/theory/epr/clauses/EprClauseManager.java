package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

public class EprClauseManager {
	
	private final ScopedHashSet<EprClause> mEprClauses = new ScopedHashSet<EprClause>();
	
	
	public void push() {
		mEprClauses.beginScope();
	}
	
	public void pop() {
		//TODO: is currentScope what we want here?? 
		// --> we only want only clauses that were added after the last beginScope
		for (EprClause ec : mEprClauses.currentScope()) {
			ec.disposeOfClause();
		}
		mEprClauses.endScope();
	}

	public void addClause(EprClause newClause) {
		mEprClauses.add(newClause);
	}

	public Iterable<EprClause> getAllClauses() {
		return mEprClauses;
	}

}
