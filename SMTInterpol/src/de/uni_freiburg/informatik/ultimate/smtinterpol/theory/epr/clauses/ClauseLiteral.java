package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.Set;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;

/**
 * Represents a literal that occurs in an EprClause.
 * This may be a ground literal or a quantified literal.
 * 
 * In contrast to the Literal class DPLLEngine uses, a 
 * ClauseLiteral has a decide state that also depends on the
 * EprStateManagers decide stack.
 * 
 * @author nutz
 */
public abstract class ClauseLiteral {


	protected final Literal mEngineLiteral;
	protected final DPLLAtom mAtom;
	protected final boolean mPolarity;
	protected final EprTheory mEprTheory;
	
	/**
	 * The clause that this ClauseLiteral is part of
	 */
	protected EprClause mEprClause;
	protected final DawgFactory<ApplicationTerm, TermVariable> mDawgFactory;
	
	public ClauseLiteral(boolean polarity, DPLLAtom atom, EprClause clause, EprTheory eprTheory) {
		mAtom = atom;
		mEngineLiteral = polarity ? atom : atom.negate();
		mPolarity = polarity;
		mEprClause = clause;
		mEprTheory = eprTheory;
		mDawgFactory = eprTheory.getDawgFactory();
	}
	
	
	public boolean getPolarity() {
		return mPolarity;
	}
	
	public Literal getLiteral() {
		return mEngineLiteral;
	}

	//
	// TODO: these three should not call determineState all the time..
	//

	public boolean isFulfillable() {
		return determineState() == ClauseLiteralState.Fulfillable;
	}

	public boolean isFulfilled() {
		return determineState() == ClauseLiteralState.Fulfilled;
	}

	public boolean isRefuted() {
		return determineState() == ClauseLiteralState.Refuted;
	}
	protected abstract ClauseLiteralState determineState();

	/**
	 * For ground clause literals this has the usual meanings wrt. the current decide state:
	 *  - fulfilled: set to true
	 *  - fulfillable: undecided
	 *  - refuted: set to false
	 *  
	 *  For quantified clause literals fulfilled/refuted means that it is true/false on all points.
	 *  Fulfillable means everything in between..
	 */
	enum ClauseLiteralState {
		Fulfilled, Fulfillable, Refuted;
	}

	public EprClause getClause() {
		return mEprClause;
	}
	
	@Override
	public String toString() {
		String negate = mPolarity ? "" : "~";
		return negate + mAtom.toString();
	}
	

	
	public abstract Clause getUnitGrounding(Literal literal) ;
//	{
//		DPLLAtom atom = literal.getAtom();
//
//		IDawg<ApplicationTerm, TermVariable> groundingDawg = null;
//		// find the matching clauseLiteral for the given literal (TODO: what if there are several?)
//		for (Entry<ClauseLiteral, IDawg<ApplicationTerm, TermVariable>> en : mClauseLitToUnitPoints.entrySet()) {
//			ClauseLiteral cl = en.getKey();
//			if (cl.getLiteral() == literal) {
//				// the literal is ground
//				assert literal.getAtom().getSMTFormula(mEprTheory.getTheory()).getFreeVars().length == 0;
//				groundingDawg = en.getValue();
//				break;
//			} else if (cl instanceof ClauseEprQuantifiedLiteral
//					&& atom instanceof EprPredicateAtom) {
//				EprPredicateAtom epa = (EprPredicateAtom) atom;
//				ClauseEprQuantifiedLiteral ceql = (ClauseEprQuantifiedLiteral) cl;
//
//				if (epa.getEprPredicate() != ceql.getEprPredicate()) {
//					continue;
//				}
//				Term[] ceqlArgs = ceql.mArgumentTerms.toArray(new Term[ceql.mArgumentTerms.size()]);
//				TTSubstitution unifier = epa.getArgumentsAsTermTuple().match(new TermTuple(ceqlArgs), mEprTheory.getEqualityManager());
//				if (unifier != null) {
//					groundingDawg = en.getValue();
//					break;
//				}
//			}
//		}
//		assert groundingDawg != null && ! groundingDawg.isEmpty();
//
//		//TODO: sample one point from the dawg, so we give a one-point dawg to getGroundings() ?..
//		
//		Set<Clause> groundings = getGroundings(groundingDawg);
//		
//		return groundings.iterator().next();
//	}
}
