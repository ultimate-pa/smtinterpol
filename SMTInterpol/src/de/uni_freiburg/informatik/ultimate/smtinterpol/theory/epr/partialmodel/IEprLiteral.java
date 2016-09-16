package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

public interface IEprLiteral {

	public EprPredicate getEprPredicate();
	
	public boolean getPolarity();
	
	public IDawg<ApplicationTerm, TermVariable> getDawg();
	
	/**
	 * To be called before this object is disposed of.
	 * Severs all links to this object that other objects may hold.
	 */
	public void unregister();
	
	public void registerConcernedClauseLiteral(ClauseEprLiteral cel);
}
