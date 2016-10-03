package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

/**
 * Interface for the commonalities of epr decide stack literals (class DecideStackLiteral)
 * (i.e. decisions internal to the epr theory, described by an epr predicate, a polarity and a dawg)
 * and epr ground literals (class EprGroundLiteral)
 * (i.e. literals over an epr predicate that are ground -- their dawg's language has cardinality 1).
 * 
 * @author Alexander Nutz
 */
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
