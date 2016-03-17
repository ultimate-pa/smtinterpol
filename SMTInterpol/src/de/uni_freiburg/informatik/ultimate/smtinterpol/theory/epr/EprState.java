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


	public EprState() {
		// TODO Auto-generated constructor stub
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
        updateClauseLiteralFulfillabilityOnPointSetting(positive, point, pred);
        return success;
	}

	/**
	 * Called when a point is set.
	 * Checks for each epr-clause if setting that point contradicts a quantified literal in the clause. 
	 * Updates that clause's status accordingly.
	 * @param settingPositive is true if this method was called because atom is being set positive, negative if atom is being
	 *  set negative
	 * @param atom
	 */
	private void updateClauseLiteralFulfillabilityOnPointSetting(boolean settingPositive, TermTuple point, EprPredicate pred) {
		for (Entry<EprClause, HashSet<Literal>> qo : pred.mQuantifiedOccurences.entrySet()) {
			EprClause clause = qo.getKey();
			for (Literal li : qo.getValue()) {
				boolean oppositeSigns = (li.getSign() == 1) ^ settingPositive;
				TermTuple otherPoint = new TermTuple(((EprPredicateAtom) li.getAtom()).getArguments());
				HashMap<TermVariable, Term> subs = point.match(otherPoint);
				if (oppositeSigns && subs != null) {
					clause.setLiteralUnfulfillable(li);
				}
			}
		}
		
	}
}
