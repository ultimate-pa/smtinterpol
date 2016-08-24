package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprGroundLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprQuantifiedLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old.EprClauseOld;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackQuantifiedLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.IDawg;

/**
 * Represents an uninterpreted predicate that the EPR theory reasons about.
 * Stores and updates a model for that predicate.
 * If setting a literal leads to a conflict, that conflict is reported.
 * 
 * @author nutz
 */
public class EprPredicate {

	public final int arity;
	public final FunctionSymbol functionSymbol;

	final EprTheory mEprTheory;
	
	/**
	 * Contains all DecideStackLiterals which talk about this EprPredicate.
	 */
	private HashSet<DecideStackQuantifiedLiteral> mDecideStackLiterals;
	
	/**
	 * Storage to track where this predicate occurs in the formula with at least one quantified argument.
	 */
	private HashMap<EprClause, HashSet<ClauseEprQuantifiedLiteral>> mQuantifiedOccurences = 
			new HashMap<EprClause, HashSet<ClauseEprQuantifiedLiteral>>();

	private HashMap<EprClause, HashSet<ClauseEprGroundLiteral>> mGroundOccurences = 
			new HashMap<EprClause, HashSet<ClauseEprGroundLiteral>>();
	
	private HashSet<EprGroundPredicateAtom> mDPLLAtoms = new HashSet<EprGroundPredicateAtom>();
	
	private HashMap<TermTuple, EprGroundPredicateAtom> mPointToAtom = new HashMap<TermTuple, EprGroundPredicateAtom>();
	private HashMap<TermTuple, EprQuantifiedPredicateAtom> mTermTupleToAtom = new HashMap<TermTuple, EprQuantifiedPredicateAtom>();

	public EprPredicate(FunctionSymbol fs, int arity, EprTheory eprTheory) {
		this.functionSymbol = fs;
		this.arity = arity;
		this.mEprTheory = eprTheory;
	}

	public void addQuantifiedOccurence(ClauseEprQuantifiedLiteral l, EprClause eprClause) {
		HashSet<ClauseEprQuantifiedLiteral> val = mQuantifiedOccurences.get(eprClause);
		if (val == null) {
			val = new HashSet<ClauseEprQuantifiedLiteral>();
			mQuantifiedOccurences.put(eprClause, val);
		}
		val.add(l);
	}
	
	public HashMap<EprClause, HashSet<ClauseEprQuantifiedLiteral>> getQuantifiedOccurences() {
		return mQuantifiedOccurences;
	}
	
	public void addGroundOccurence(ClauseEprGroundLiteral l, EprClause eprClause) {
		HashSet<ClauseEprGroundLiteral> val = mGroundOccurences.get(eprClause);
		if (val == null) {
			val = new HashSet<ClauseEprGroundLiteral>();
			mGroundOccurences.put(eprClause, val);
		}
		val.add(l);
	}
	
	public HashMap<EprClause, HashSet<ClauseEprGroundLiteral>> getGroundOccurences() {
		return mGroundOccurences;
	}

	public void addDPLLAtom(EprGroundPredicateAtom egpa) {
		mDPLLAtoms.add(egpa);
	}
	
	public HashSet<EprGroundPredicateAtom> getDPLLAtoms() {
		return mDPLLAtoms;
	}
	
	/**
	 * Retrieve the ground atom belonging to TermTuple tt.
	 * Creates a new atom if no atom exists for tt.
	 * Note: this method assumes that tt only contains constants.
	 * Use getAtomForTermTuple in order to obtain a quantified atom.
	 */
	public EprGroundPredicateAtom getAtomForPoint(TermTuple point, Theory mTheory, int assertionStackLevel) {
		assert point.getFreeVars().size() == 0 : "Use getAtomForTermTuple, if tt is quantified";
		EprGroundPredicateAtom result = mPointToAtom.get(point);
		if (result == null) {
			ApplicationTerm newTerm = mTheory.term(this.functionSymbol, point.terms);
			result = new EprGroundPredicateAtom(newTerm, 0, //TODO: hash
					assertionStackLevel,
					this);
			mPointToAtom.put(point, result);
			addDPLLAtom(result);
		}
		return result;
	}

	/**
	 * Retrieve the quantified atom belonging to TermTuple tt.
	 * Creates a new atom if no atom exists for tt.
	 * Note: this method assumes that tt has at least one TermVariable (i.e. is quantified).
	 * Use getAtomForPoint in order to obtain a ground atom.
	 * @param tt
	 * @param mTheory
	 * @param assertionStackLevel
	 * @return
	 */
	public EprQuantifiedPredicateAtom getAtomForTermTuple(TermTuple tt, Theory mTheory, int assertionStackLevel) {
		assert tt.getFreeVars().size() > 0 : "Use getAtomForPoint, if tt is ground";
		EprQuantifiedPredicateAtom result = mTermTupleToAtom.get(tt);
		
		if (result == null) {
			ApplicationTerm newTerm = mTheory.term(this.functionSymbol, tt.terms);
			result = new EprQuantifiedPredicateAtom(newTerm, 0, //TODO: hash
					assertionStackLevel,
					this);
			mTermTupleToAtom.put(tt, result);
		}
		return result;
	}
	
	public String toString() {
		return "EprPred: " + functionSymbol.getName();
	}

	public EprGroundPredicateAtom getAtomForPoint(TermTuple point) {
		EprGroundPredicateAtom result = mPointToAtom.get(point);
		assert result != null;
		return result;
	}

//	public boolean isModelComplete() {
//		assert false : "TODO: implement";
//		return false;
//	}

	/**
	 * Attempts to complete the current partial model (provided by the decides stack)
	 * for this EprPredicate.
	 * Returns null in the case of success and a ground conflict clause otherwise;
	 * 
	 * TODO: Question: what can this return? Only ground clauses? EprClauses? Something that 
	 *  needs a dawg??
	 * @return
	 */
	public Object completeModel() {
		
		IDawg positivelySetPoints = null;
		IDawg negativelySetPoints = null;
		IDawg undecidedPoints = null;

		for (DecideStackQuantifiedLiteral dsl : mDecideStackLiterals) {
			if (dsl.getPolarity()) {
				//positive literal
				positivelySetPoints.addAll(dsl.getDawg());
			} else {
				//negative literal
				negativelySetPoints.addAll(dsl.getDawg());
			}
		}
		
		// the ground predicates' decide statusses are managed by the DPLLEngine
		for (EprGroundPredicateAtom at : mDPLLAtoms) {
			if (at.getDecideStatus() == null) {
				// not yet decided
				undecidedPoints.add(at.getArguments());
			} else if (at.getDecideStatus().getSign() == 1) {
				// positively set
				positivelySetPoints.add(at.getArguments());
			} else {
				// negatively set
				negativelySetPoints.add(at.getArguments());
			}
			
		}
		
		IDawg allDecidedPoints = null;
		allDecidedPoints.addAll(positivelySetPoints);
		allDecidedPoints.addAll(negativelySetPoints);
		
		undecidedPoints.addAll(allDecidedPoints.complement());
		
		
		if (undecidedPoints.isEmpty()) {
			return null;
		} else {
			Object conflict = mEprTheory.getStateManager().setEprDecideStackLiteral(
					new DecideStackQuantifiedLiteral(true, this, undecidedPoints));
			return conflict;
		}
	}

	/**
	 * Called when an EprClause is disposed of (typically because of a pop command).
	 * Updates internal data structures of this EprPredicate accordingly.
	 * 
	 * @param eprClause
	 */
	public void notifyAboutClauseDisposal(EprClause eprClause) {
		mQuantifiedOccurences.remove(eprClause);
		mGroundOccurences.remove(eprClause);
	}


}
