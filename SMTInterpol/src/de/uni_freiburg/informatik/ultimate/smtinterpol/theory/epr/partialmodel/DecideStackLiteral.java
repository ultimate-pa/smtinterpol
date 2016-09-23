package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

/**
 * Represents a literal on the DPLL decide stack of the EprTheory.
 * This special literal consists of a quantified literal together with a 
 * data structure restricting the possible groundings of that literal.
 * 
 * @author Alexander Nutz
 */
public abstract class DecideStackLiteral implements IEprLiteral, Comparable<DecideStackLiteral> {
	
//	/**
//	 * The index on the decide stack of its push state that this DecideStackLiteral has.
//	 */
//	protected final int mIndexOnPushStateStack;
//	
//	/**
//	 * The index of the push state on the stateManager's push state stack
//	 */
//	protected final int mPushStateStackIndex;
	
	protected final DslIndex mIndex;

	protected final boolean mPolarity;
	protected final EprPredicate mPred;
	
	/**
	 * Stores all the groundings for which this.atom is decided with this.polarity
	 * by this DecideStackLiteral
	 */
	protected IDawg<ApplicationTerm, TermVariable> mDawg;
	
	protected Set<ClauseEprLiteral> mConcernedClauseLiterals = new HashSet<ClauseEprLiteral>();
	
	
	
	public DecideStackLiteral(boolean polarity, 
			EprPredicate pred, IDawg<ApplicationTerm, TermVariable> dawg, Pair<Integer, Integer> index) {
		mPolarity = polarity;
		mPred = pred;
		mDawg = dawg;
//		mPushStateStackIndex = index.first;
//		mIndexOnPushStateStack = index.second;
		mIndex = new DslIndex(index.first, index.second);
		
		register();
	}
	
	@Override
	public boolean getPolarity() {
		return mPolarity;
	}
	
	@Override
	public EprPredicate getEprPredicate() {
		return mPred;
	}

	/**
	 * Checks if this literal's dawg talks about the point described by arguments.
	 * arguments may only contain constants.
	 * @param arguments
	 * @return
	 */
	public boolean talksAboutPoint(Term[] arguments) {
		assert false : "TODO: implement";
		return false;
	}
	
	@Override
	public IDawg<ApplicationTerm, TermVariable> getDawg() {
		return mDawg;
	}
	
	/**
	 * 
	 * @return true iff mDawg's language is a singleton set.
	 */
	public boolean isOnePoint() {
		return mDawg.isSingleton();
	}
	
	public List<ApplicationTerm> getPoint() {
		assert isOnePoint();
		return mDawg.iterator().next();
	}
	
	private void register() {
		mPred.registerEprLiteral(this);
	}

	/**
	 * This is called when this dsl is removed from the decide stack.
	 * It should purge this dsl from every data structure where it was registered.
	 */
	@Override
	public void unregister() {
		mPred.unregisterEprLiteral(this);
		for (ClauseEprLiteral cl : mConcernedClauseLiterals) {
			cl.unregisterIEprLiteral(this);
		}
	}
	
	@Override
	public void registerConcernedClauseLiteral(ClauseEprLiteral cel) {
		mConcernedClauseLiterals.add(cel);
	}
	
//	/**
//	 * @return
//	 */
//	public int getPushStateDecideStackIndex() {
//		return mIndexOnPushStateStack;
//	}
//	
//	public int getPushStateIndex() {
//		return mPushStateStackIndex;
//	}
	
	public DslIndex getIndex() {
		return mIndex;
	}
	
	@Override
	public int compareTo(DecideStackLiteral other) {
		return this.mIndex.compareTo(other.mIndex);
	}
	
	static class DslIndex implements Comparable<DslIndex> {
		
		final int indexOfPushState;
		final int indexOnPushStatesDecideStack;
		
		public DslIndex(int indexOfPushState, int indexOfPushStatesDecideStack) {
			this.indexOfPushState = indexOfPushState;
			this.indexOnPushStatesDecideStack = indexOfPushStatesDecideStack;
		}

		/**
		 * DslIndices are compared lexicographically. First, the index of the push state a dsl is on
		 * is compared. Only if that is equal the positions of the two literals on that push state's 
		 * decide stack is compared.
		 */
		@Override
		public int compareTo(DslIndex o) {
			int comp1 = Integer.compare(this.indexOfPushState, o.indexOfPushState);
			if (comp1 == 0) {
				return Integer.compare(this.indexOnPushStatesDecideStack, o.indexOnPushStatesDecideStack);
			} 
			return comp1;
		}
		
	}
}
