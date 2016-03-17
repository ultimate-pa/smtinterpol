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

	ArrayList<EprClause> mDerivedClauses = new ArrayList<EprClause>();

	ArrayList<Literal> mSetLiterals = new ArrayList<>();
	
	HashMap<EprPredicate, EprPredicateModel> mPredicateToModel = new HashMap<>();


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
	public boolean setPoint(boolean positive, EprGroundPredicateAtom atom) {
		EprPredicate pred = atom.eprPredicate;
        TermTuple point = new TermTuple(((EprPredicateAtom) atom).getArguments());

        boolean success;
        if (positive)
        	success = mPredicateToModel.get(pred).setPointPositive(point);
        else
        	success = mPredicateToModel.get(pred).setPointNegative(point);
        assert success;
        
        pred.mPointToAtom.put(point, atom);
        
        return success;
	}



	public void addNewEprPredicate(EprPredicate pred) {
		mPredicateToModel.put(pred, new EprPredicateModel(pred));
	}
}
