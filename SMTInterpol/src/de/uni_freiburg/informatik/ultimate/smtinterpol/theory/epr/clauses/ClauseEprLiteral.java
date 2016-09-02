package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

public abstract class ClauseEprLiteral extends ClauseLiteral {

	EprPredicateAtom mEprPredicateAtom;
	
	/**
	 * The literals on the current epr decide stack that contradict this literal at
	 * least on one point, potentially on many or all points that this literal talks about.
	 * (e.g. when P(a,x) is on the decide stack it contradicts ~P(y,b) on the point (a,b).)
	 */
	ScopedHashSet<DecideStackLiteral> mPartiallyConflictingDecideStackLiterals = 
			new ScopedHashSet<DecideStackLiteral>();
	
	ScopedHashSet<DecideStackLiteral> mPartiallyFulfillingDecideStackLiterals = 
			new ScopedHashSet<DecideStackLiteral>();


	public ClauseEprLiteral(boolean polarity, EprPredicateAtom atom, EprClause clause, EprTheory eprTheory) {
		super(polarity, atom, clause, eprTheory);
		mEprPredicateAtom = atom;
	}


	public EprPredicate getEprPredicate()  {
		return  mEprPredicateAtom.getEprPredicate();
	}
	
	
	public void addPartiallyConflictingDecideStackLiteral(DecideStackLiteral dsl) {
		assert (! (this instanceof ClauseEprGroundLiteral)) || dsl.talksAboutPoint(this.mEprPredicateAtom.getArguments());
		mPartiallyConflictingDecideStackLiterals.add(dsl);
	}

	public void removePartiallyConflictingDecideStackLiteral(DecideStackLiteral dsl) {
		mPartiallyConflictingDecideStackLiterals.remove(dsl);
	}
	
	public void addPartiallyFulfillingDecideStackLiteral(DecideStackLiteral dsl) {
		assert (! (this instanceof ClauseEprGroundLiteral)) || dsl.talksAboutPoint(this.mEprPredicateAtom.getArguments());
		mPartiallyFulfillingDecideStackLiterals.add(dsl);
	}
	
	public ScopedHashSet<DecideStackLiteral> getPartiallyConflictingDecideStackLiterals() {
		return mPartiallyConflictingDecideStackLiterals;
	}

	public void removePartiallyFulfillingDecideStackLiteral(DecideStackLiteral dsl) {
		mPartiallyFulfillingDecideStackLiterals.remove(dsl);
	}
	
	/**
	 * notifies the clause about the beginning of a push/pop scope
	 */
	public void beginScope() {
		mPartiallyConflictingDecideStackLiterals.beginScope();
		mPartiallyFulfillingDecideStackLiterals.beginScope();
	}
	
	/**
	 * notifies the clause about the ending of a push/pop scope
	 */
	public void endScope() {
		mPartiallyConflictingDecideStackLiterals.endScope();
		mPartiallyFulfillingDecideStackLiterals.endScope();
	}
}
