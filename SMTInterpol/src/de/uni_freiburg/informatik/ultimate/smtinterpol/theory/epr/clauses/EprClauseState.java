package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

/**
 * The states that an EprClause can have, it can be
 *  - fulfilled: at least one literal is fulfilled (on all points)
 *  - "normal": no literal is fulfilled on all points, there is no point where the clause is unit or a conflict
 *  - unit: on at least one point all literals except one are refuted, that one is unconstrained
 *  - conflict: on at least one point all literals are refuted
 *  
 * @author nutz
 */
public enum EprClauseState {
	Fulfilled, Normal, Unit, Conflict
}
