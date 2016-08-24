package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

/**
 * The states that an EprClause can have, it can be
 *  - fulfilled: at least one literal is fulfilled
 *  - "normal": two or more literals are unconstrained, none is fulfilled
 *  - unit: all literals except one are refuted, that one is unconstrained
 *  - conflict: all literals are refuted
 * @author alex
 *
 */
public enum EprClauseState {
	Fulfilled, Normal, Unit, Conflict
}
