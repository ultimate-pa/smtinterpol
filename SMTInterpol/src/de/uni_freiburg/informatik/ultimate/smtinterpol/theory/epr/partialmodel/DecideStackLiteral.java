package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

/**
 * Represents a literal on the DPLL decide stack of the EprTheory.
 * This special literal consists of a quantified literal together with a 
 * data structure restricting the possible groundings of that literal.
 * 
 * @author nutz
 */
public abstract class DecideStackLiteral {

	boolean mPolarity;
//	EprPredicateAtom mAtom;
	EprPredicate mPred;
	
	/**
	 * Stores all the groundings for which this.atom is decided with this.polarity
	 * by this DecideStackLiteral
	 */
	IDawg<ApplicationTerm, TermVariable> mDawg;
	

//	public DecideStackLiteral(boolean polarity, EprQuantifiedPredicateAtom atom) {
//		mPolarity = polarity;
//		mAtom = atom;
//		mPred = mAtom.getEprPredicate();
//	}

	

	public DecideStackLiteral(boolean polarity, 
			EprPredicate pred, IDawg<ApplicationTerm, TermVariable> dawg) {
		mPolarity = polarity;
		mPred = pred;
		mDawg = dawg;
		
		register();
	}
	
	public boolean getPolarity() {
		return mPolarity;
	}
	
//	public EprPredicateAtom getAtom() {
//		return mAtom;
//	}
//	
//	public Literal getLiteral() {
//		return mPolarity ? mAtom : mAtom.negate();
//	}
	
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
	
	public IDawg<ApplicationTerm, TermVariable> getDawg() {
		return mDawg;
	}
	
	/**
	 * 
	 * @return true iff mDawg's language is a singleton set.
	 */
	public boolean isOnePoint() {
		assert false : "TODO: implement";
		return false;
	}
	
	public List<ApplicationTerm> getPoint() {
		assert isOnePoint();
		assert false : "TODO: implement";
		return null;
	}
	
	private void register() {
		mPred.addDecideStackLiteral(this);
	}

	/**
	 * This is called when this dsl is removed from the decide stack.
	 * It should purge this dsl from every data structure where it was registered.
	 */
	public void unregister() {
		mPred.removeDecideStackLiteral(this);
	}
}
