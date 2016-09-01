package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
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

//	public IDawg<LETTER, COLNAMES> createEmptyDawg(COLNAMES[] termVariables) {
	public IDawg<LETTER, COLNAMES> createEmptyDawg(List<COLNAMES> termVariables) {
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
	public IDawg<LETTER, COLNAMES> createFullDawg(List<COLNAMES> termVariables) {
		assert termVariables != null;
		return new NaiveDawg<LETTER, COLNAMES>(termVariables, mAllConstants).complement();
	}

	public IDawg<LETTER, COLNAMES> copyDawg(IDawg<LETTER, COLNAMES> dawg) {
		NaiveDawg<LETTER, COLNAMES> nd = (NaiveDawg<LETTER, COLNAMES>) dawg;
		return new NaiveDawg<LETTER, COLNAMES>(nd);
	}
	
	
	/**
	 * Returns a dawg that is the same as the input dawg, but the columns have been renamed according 
	 * to the given map.
	 * @param dawg
	 * @param translation
	 * @return
	 */
	public IDawg<LETTER, COLNAMES> renameColumnsOfDawg(
//			IDawg<LETTER, COLNAMES> dawg, DawgTranslation<COLNAMES> translation) {
			IDawg<LETTER, COLNAMES> dawg, Map<COLNAMES, COLNAMES> translation) {
		NaiveDawg<LETTER, COLNAMES> nd = (NaiveDawg<LETTER, COLNAMES>) dawg;
		return new NaiveDawg<LETTER, COLNAMES>(nd, translation);
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

	/**
	 * Computes a Dawgs that represents a natural join on two Dawgs. 
	 * Also allows to give a renaming for the columns second dawg that is applied before the join.
	 * The column names taken for the natural join are the COLNAMES of the dawgs.
	 * 
	 * @param d1
	 * @param d2
	 * @param translation is applied to d2. Allows to rename its columns before the join.
	 * @return
	 */
	public IDawg<LETTER, COLNAMES> join(IDawg<LETTER, COLNAMES> d1,
			IDawg<LETTER, COLNAMES> d2,
			Map<COLNAMES, COLNAMES> translation) {
		/*
		 * - align the column names by the translation
		 * - make a new joint signature
		 * - create a dawg over the new signature
		 * - add the points
		 */
		IDawg<LETTER, COLNAMES> rnd2 = 
				 renameColumnsOfDawg(d2, translation);
		
		List<COLNAMES> newSignature = new ArrayList<COLNAMES>(d1.getColnames());
		for (COLNAMES cn : rnd2.getColnames()) {
			if (!newSignature.contains(cn)) {
				newSignature.add(cn);
			}
		}
		
		// right now: work with NaiveDawgs
		IDawg<LETTER, COLNAMES> newDawg = 
				(NaiveDawg<LETTER, COLNAMES>) createEmptyDawg(newSignature);
		
		newDawg.addAllWithSubsetSignature(d1);
		newDawg.addAllWithSubsetSignature(rnd2);
		
		return null;
	}

	/**
	 * Create a dawg from the input dawg where only the points are selected that match the given mapping.
	 * 
	 * @param dawg
	 * @param selectMap (possibly) restricts some COLNAMES in the signature to only one LETTER
	 * @return
	 */
	public IDawg<ApplicationTerm, TermVariable> select(IDawg<ApplicationTerm, TermVariable> dawg,
			Map<TermVariable, ApplicationTerm> selectMap) {
		return dawg.select(selectMap);
	}


//	public IDawg<LETTER, COLNAMES> translateDawg(IDawg<LETTER, COLNAMES> dawg,
//			DawgTranslation<COLNAMES> translation) {
//		IDawg<LETTER, COLNAMES> nd = createEmptyDawg(translation.getNewSignature());
//		nd.addAll(dawg);
//		if (nd instanceof NaiveDawg<?, ?>) {
//			nd.
//		}
//		return null;
//	}
	
}
