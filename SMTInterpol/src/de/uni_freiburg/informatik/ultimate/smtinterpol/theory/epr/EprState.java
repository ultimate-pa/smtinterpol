package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

/**
 * Represents a partial model for the parts of the EprTheory 
 * (EprClause, set EprAtoms, EprPredicate models).
 * 
 * Is used to track the different parts of a model that correspond to each 
 * decide state in the DPLLEngine (e.g. a setLiteral may trigger the introduction of 
 * new EprClauses..)
 */
public class EprState {

	/**
	 * Set of Clauses that is derivable in the current state.
	 * TODO: think more about this.
	 *   -- if the clause is ground, add it to the theory?? Probably not, because we would need to remove it, when popping this state..
	 */
	ArrayList<EprNonUnitClause> mDerivedClauses = new ArrayList<>();

	/**
	 * Base clauses, i.e., clauses that came in through an assert. 
	 * (state dependent as soon as we support push/pop
	 */
	ArrayList<EprNonUnitClause> mBaseClauses = new ArrayList<>();

//	ArrayList<EprQuantifiedLitWExcptns> mSetLiterals = new ArrayList<>();
	
	HashMap<EprPredicate, EprPredicateModel> mPredicateToModel = new HashMap<>();

	private ArrayList<EprClause> mConflictClauses = new ArrayList<>();

	/**
	 * constructor for the base state
	 */
	public EprState() {
		// TODO Auto-generated constructor stub
	}

	/**
	 * constructor for a non-base state
	 */
	public EprState(EprState previousState) {
		// this state needs to know about all the predicates of the previous state (some more might be added, later, too..)
		for (EprPredicate pred : previousState.mPredicateToModel.keySet())
			mPredicateToModel.put(pred, new EprPredicateModel(pred));
	}

	/**
	 * If the current model allows it, set the given point in the predicate model to "true", return true;
	 * If the point was already set to false, we have a conflict, do nothing, return false.
	 * @param atom
	 * @return
	 */
	public void setPoint(boolean positive, EprGroundPredicateAtom atom) {
		EprPredicate pred = atom.eprPredicate;
        TermTuple point = new TermTuple(((EprPredicateAtom) atom).getArguments());

        if (positive)
        	mPredicateToModel.get(pred).setPointPositive(point);
        else
        	mPredicateToModel.get(pred).setPointNegative(point);
	}

	public void setQuantifiedLiteralWithExceptions(EprQuantifiedUnitClause eqlwe) {
		EprPredicate pred = eqlwe.getPredicateAtom().eprPredicate;

        if (eqlwe.getPredicateLiteral().getSign() == 1)
        	mPredicateToModel.get(pred).setQuantifiedLitPositive(eqlwe);
        else
        	mPredicateToModel.get(pred).setQuantifiedLitNegative(eqlwe);
	}
	
	public void unsetQuantifiedLiteralWithExceptions(EprQuantifiedUnitClause eqlwe) {
		EprPredicate pred = eqlwe.getPredicateAtom().eprPredicate;

		mPredicateToModel.get(pred).unsetQuantifiedLitPositive(eqlwe);
	}

	/**
	 * NOTE: in contrast to non-derived EprClauses the derived ones may lack any free variables
	 * @param ec
	 * @return true if ec is a conflict clause, false otherwise
	 */
	public boolean addDerivedClause(EprNonUnitClause ec) {
		mDerivedClauses.add(ec);
		return addClause(ec, false);
	}

	/**
	 * @param bc
	 * @return true if bc is a conflict clause, false otherwise
	 */
	public boolean addBaseClause(EprNonUnitClause bc) {
		mBaseClauses.add(bc);
		return addClause(bc, true);
	}
	
	private boolean addClause(EprNonUnitClause c, boolean base) {
		if (c.isConflictClause()) {
			mConflictClauses.add(c);
			return true;
		}
		return false;
	}
	

	public void addNewEprPredicate(EprPredicate pred) {
		mPredicateToModel.put(pred, new EprPredicateModel(pred));
	}
	
	public ArrayList<EprNonUnitClause> getDerivedClauses() {
		return mDerivedClauses;
	}
	
	public ArrayList<EprNonUnitClause> getBaseClauses() {
		return mBaseClauses;
	}

	public ArrayList<EprClause> getConflictClauses() {
		return mConflictClauses;
	}
}
