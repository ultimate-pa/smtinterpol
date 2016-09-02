package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

public class EprClauseFactory {
	
	EprTheory mEprTheory;
	
	/**
	 * Remembers from which sets of literals an EprClause has already been 
	 * constructed (and which).
	 */
	private ScopedHashMap<Set<Literal>, EprClause> mLiteralsToClause = new ScopedHashMap<Set<Literal>, EprClause>();
	
	public EprClauseFactory(EprTheory eprTheory) {
		mEprTheory = eprTheory;
	}
		
	/**
	 * 
	 * @param pivot1 A ClauseLiteral of c1, the pivot on the side of c1
	 * @param pivot2 A ClauseLiteral that was used for propagation, 
	 *          its clause is the other clause for the resolution, thie parameter is the pivot on that side
	 * @return the resolvent of c1 and clauseLiteral.clause with pivot conflit
	 */
	public EprClause createResolvent(ClauseEprQuantifiedLiteral pivot1, ClauseLiteral pivot2) {
		assert pivot1.getPolarity() != pivot2.getPolarity();
		EprClause c1 = pivot1.getClause();
		EprClause c2 = pivot2.getClause();

		//TODO rework
		
		/*
		 * plan:
		 *  - compute unifier for the pivot literals
		 *  - apply the unifier to all literals in one of the clauses
		 *  - construct the resolvent from the literals
		 */

//		Set<ClauseLiteral> litsForResolvent = new HashSet<ClauseLiteral>();
//		litsForResolvent.addAll(c1.getLiterals());
//		litsForResolvent.remove(pivot1);
//		litsForResolvent.addAll(c2.getLiterals());
//		litsForResolvent.remove(pivot2);
//		
//		HashSet<Literal> lfr = new HashSet<Literal>();
//		for (ClauseLiteral cl : litsForResolvent) {
//			lfr.add(cl.getLiteral());
//		}
//		
//		return getClause(lfr);
		return null;
	}
	
	/**
	 * makes sure that for the same set of literals only one clause is constructed.
	 * Note that this may return a EprDerivedClause -- if there already is one for the set of Literals
	 * (copy from the old getBaseClause method)
	 */
	public EprClause getClause(Set<Literal> newLits) {
		EprClause result = mLiteralsToClause.get(newLits);
		if (result == null) {
			result = new EprClause(newLits, mEprTheory);
			mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): creating new clause " + result);
			mLiteralsToClause.put(newLits, result);
		} else {
			mEprTheory.getLogger().debug("EPRDEBUG (EprStateManager): clause has been added before " + result);
		}
		return result;
	}
	
	public void push() {
		mLiteralsToClause.beginScope();
	}
	
	public void pop() {
		mLiteralsToClause.endScope();
	}
}
