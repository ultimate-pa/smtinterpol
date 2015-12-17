package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

/**
 * Represents an uninterpreted predicate that the EPR theory reasons about.
 * Stores and updates a model for that predicate.
 * If setting a literal leads to a conflict, that conflict is reported.
 * 
 * @author Alexander Nutz
 */
public class EprPredicate {

	public final FunctionSymbol functionSymbol;

	public final int arity;
	
	private HashSet<TermTuple> mPositivelySetPoints = new HashSet<>();
	private HashSet<TermTuple> mNegativelySetPoints = new HashSet<>();
	
	
//	private ArrayList<EprAlmostAllAtom> mAlmostAllAtoms;
//	private ArrayList<Literal> mAlmostAllAtoms;
	
	/*
	 * Storage to track where this predicate occurs in the formula with at least one quantified argument.
	 */
	HashMap<EprClause, HashSet<Literal>> mQuantifiedOccurences = new HashMap<>();

	private HashSet<EprAlmostAllAtom> mPositiveAlmostAllAtoms = new HashSet<>();
	private HashSet<EprAlmostAllAtom> mNegativeAlmostAllAtoms = new HashSet<>();


	
	public EprPredicate(FunctionSymbol fs, int arity) {
		this.functionSymbol = fs;
		this.arity = arity;
	}
	
	/**
	 * If the current model allows it, set the given point in the predicate model to "true", return true;
	 * If the point was already set to false, we have a conflict, do nothing, return false.
	 * @param point
	 * @return
	 */
	public boolean setPointPositive(TermTuple point) {
//		assert !mNegativelySetPoints.contains(point) : "is that ok??";
		if (!mNegativelySetPoints.contains(point)) {
			return false;
		} else {
			mPositivelySetPoints.add(point);
			return true;
		}
	}

	/**
	 * If the current model allows it, set the given point in the predicate model to "false", return true;
	 * If the point was already set to false, we have a conflict, do nothing, return false.
	 * @param point
	 * @return
	 */
	public boolean setPointNegative(TermTuple point) {
//		assert !mPositivelySetPoints.contains(point) : "is that ok??";
		if (!mPositivelySetPoints.contains(point)) {
			return false;
		} else {
			mNegativelySetPoints.add(point);
			return true;
		}
	}
	
	public String toString() {
		return "EprPred: " + functionSymbol.getName();
	}

	public void unSetPointPositive(TermTuple point) {
		assert mPositivelySetPoints.contains(point) : "backtracking a point that was not set";
		mPositivelySetPoints.remove(point);
	}
	
	public void unSetPointNegative(TermTuple point) {
		assert mNegativelySetPoints.contains(point) : "backtracking a point that was not set";
		mNegativelySetPoints.remove(point);
	}

	/**
	 * Answers the question, if, 
	 *  - in the current decide state (communicated through setPoint-methods),
	 *  - given some excepted variables where we don't care (because of equalities in the clause),
	 *  - given a sign of the literal in which the predicate occurs in the current clause,
	 * this predicate is "true".
	 * @param isLiteralPositive true, iff, the literal occurs positive in the clause
	 * @param exceptedConstants constants where we don't need to fulfill the predicate
	 */
	public boolean check(boolean isLiteralPositive, ApplicationTerm[] exceptedConstants) {
		// TODO Auto-generated method stub
		
		return false; //TODO return correct value
	}
	
	public void addQuantifiedOccurence(Literal l, EprClause eprClause) {
		HashSet<Literal> val = mQuantifiedOccurences.get(eprClause);
		if (val == null) {
			val = new HashSet<>();
			mQuantifiedOccurences.put(eprClause, val);
		}
		val.add(l);
	}
//	
//	public HashMap<EprClause,HashSet<Literal>> getQuantifiedOccurences() {
//		return mQuantifiedOccurences;
//	}

	/**
	 * Update the model such that atom is set.
	 * This may return a conflict in form of a clause over almost-all atoms if the newly
	 * set atom contradicts the current model.
	 * (example: atom = <P v1 v2>, mAlmostAllAtoms = [(not <P v1 v1>)] will yield the conflict clause
	 *  {(not <P v1 v2>), <P v1 v1>})
	 * @param atom the almost-all atom that is to be set positively in the model
	 * @return conflict clause if there is a conflict with the current model, otherwise null
	 */
	public Clause setAlmostAllAtomPositive(EprAlmostAllAtom atom) {
		mPositiveAlmostAllAtoms.add(atom);
		assert !mNegativeAlmostAllAtoms.contains(atom) : 
			"DPLL sets that atom both positively and negatively? --> this cannot be, right?";

		//check for conflicts with current model
		for (EprAlmostAllAtom aaa : mNegativeAlmostAllAtoms) {
			//case: setting <P ...>, already set (not <P ...>)
			if (atom.signatureImplies(aaa)) {
				//case: setting <P x y>, already set (not <P x x>)
				// conflict clause: {(not <P x y>), <P x x>}, i.e. <P x y> ==> <P x x>
				Literal[] lits = new Literal[2];
				lits[0] = atom.negate();
				lits[1] = aaa;
				return new Clause(lits);
			}
		}
			
		//no conflict detected
		return null;
	}

	/**
	 * Update the model such that atom is set.
	 * This may return a conflict in form of a clause over almost-all atoms if the newly
	 * set atom contradicts the current model.
	 * @param atom the almost-all atom that is to be set negatively in the model
	 * @return conflict clause if there is a conflict with the current model, otherwise null
	 */
	public Clause setAlmostAllAtomNegative(EprAlmostAllAtom atom) {
		//(dual to positive case, of course)
		mNegativeAlmostAllAtoms.add(atom);
		assert !mPositiveAlmostAllAtoms.contains(atom) : 
			"DPLL sets that atom both positively and negatively? --> this cannot be, right?";

		//check for conflicts with current model
		for (EprAlmostAllAtom aaa : mPositiveAlmostAllAtoms) {
			//case: setting (not <P ...>), already set <P ...>
			if (atom.signatureImplies(aaa)) {
				//case: setting (not <P x y>), already set <P x x>
				// conflict clause: { <P x y>, (not <P x x>)}, i.e. (not <P x y>) ==> (not <P x x>)
				Literal[] lits = new Literal[2];
				lits[0] = atom;
				lits[1] = aaa.negate();
				return new Clause(lits);
			}
		}
			
		//no conflict detected
		return null;

	}

	public void unSetAlmostAllAtomPositive(EprAlmostAllAtom atom) {
		mPositiveAlmostAllAtoms.remove(atom);
	}

	public void unSetAlmostAllAtomNegative(EprAlmostAllAtom atom) {
		mNegativeAlmostAllAtoms.remove(atom);
	}
	
//	/*
//	 * Special predicate that describes the value the current EPR predicate has at
//	 * almost all positions.
//	 */
//	DPLLAtom mAlmostAllAtom;
////	EprPredicateAtom mAlmostAllAtom;
//
//	public DPLLAtom getAlmostAllAtom(Clausifier cl) {
//		if (mAlmostAllAtom == null) {
//			//TODO: is this the right way to introduce a literal??..
//			Term boolConst = cl.getTheory().constant("AA_" + mFunctionSymbol.toString(), cl.getTheory().getBooleanSort());
//			mAlmostAllAtom = cl.getCreateLiteral(boolConst).getAtom();
//		}
//		return mAlmostAllAtom;
//	}
}
