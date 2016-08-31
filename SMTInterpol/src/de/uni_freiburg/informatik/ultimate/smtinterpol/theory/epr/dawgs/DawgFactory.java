package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;

public class DawgFactory<LETTER, COLNAMES> {
	
	EprTheory mEprTheory;
	Set<LETTER> mAllConstants;
	
	public DawgFactory(Set<LETTER> allConstants, EprTheory eprTheory) {
		mEprTheory = eprTheory;
		mAllConstants = allConstants;
	}

	public IDawg<LETTER, COLNAMES> createEmptyDawg(COLNAMES[] termVariables) {
		assert termVariables != null;
		//TODO freeze the current allConstants set, here?? or can it just change transparently?? 
		return new NaiveDawg<LETTER, COLNAMES>(termVariables, mAllConstants);
	}

	public IDawg<LETTER, COLNAMES> createEmptyDawg(int arity) {
		assert false : "TODO: implement";
		return null;
	}

	/**
	 * Creates and returns a Dawg that accepts all words in Sigma^n.
	 * (where n = termVariables.length)
	 *
	 * @param termVariables
	 * @return
	 */
	public IDawg<LETTER, COLNAMES> createFullDawg(COLNAMES[] termVariables) {
		assert termVariables != null;
		return new NaiveDawg<LETTER, COLNAMES>(termVariables, mAllConstants).complement();
	}

	public IDawg<LETTER, COLNAMES> copyDawg(IDawg<LETTER, COLNAMES> dawg) {
		NaiveDawg<LETTER, COLNAMES> nd = (NaiveDawg<LETTER, COLNAMES>) dawg;
		return new NaiveDawg<LETTER, COLNAMES>(nd);
	}

	public IDawg<LETTER, COLNAMES> createJoinDawg(Map<ClauseLiteral, DecideStackLiteral> mHistory,
			ClauseLiteral mWatchedLiteral) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * Join two dawgs where the column labels are just the position -- i.e., basically ignore the column names..
	 * @param points
	 * @param dawg
	 * @return
	 */
	public IDawg<LETTER, COLNAMES> joinByPosition(IDawg<LETTER, COLNAMES> points,
			IDawg<LETTER, COLNAMES> dawg) {
		// TODO Auto-generated method stub
		return null;
	}
	
}
