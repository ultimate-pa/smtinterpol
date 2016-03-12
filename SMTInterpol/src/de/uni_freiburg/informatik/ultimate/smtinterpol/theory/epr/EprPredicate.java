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
	
	HashSet<TermTuple> mPositivelySetPoints = new HashSet<>();
	HashSet<TermTuple> mNegativelySetPoints = new HashSet<>();
	
	// idea: every domain is nonempty, so we always have to decide the value of a predicate on 
	// a point (lambda, lambda, ...) 
	// (lambda may be equal to other constants appearing in the formula, but if there is none, we need this point for our domain)
	boolean valueOnLambda = false;
	
	/**
	 * Storage to track where this predicate occurs in the formula with at least one quantified argument.
	 */
	HashMap<EprClause, HashSet<Literal>> mQuantifiedOccurences = new HashMap<>();
	
	HashMap<TermTuple, EprPredicateAtom> mPointToAtom = new HashMap<TermTuple, EprPredicateAtom>();

	public EprPredicate(FunctionSymbol fs, int arity) {
		this.functionSymbol = fs;
		this.arity = arity;
	}
	
	/**
	 * If the current model allows it, set the given point in the predicate model to "true", return true;
	 * If the point was already set to false, we have a conflict, do nothing, return false.
	 * @param atom
	 * @return
	 */
	public boolean setPointPositive(EprPredicateAtom atom) {
        TermTuple point = new TermTuple(((EprPredicateAtom) atom).getArguments());
//		assert !mNegativelySetPoints.contains(point) : "is that ok??";
		if (mNegativelySetPoints.contains(point)) {
			return false;
		} else {
			mPointToAtom.put(point, atom);
			mPositivelySetPoints.add(point);
			updateClauseLiteralFulfillabilityOnPointSetting(true, point);
			return true;
		}
	}


	/**
	 * If the current model allows it, set the given point in the predicate model to "false", return true;
	 * If the point was already set to false, we have a conflict, do nothing, return false.
	 * @param point
	 * @return
	 */
	public boolean setPointNegative(EprPredicateAtom atom) {
        TermTuple point = new TermTuple(((EprPredicateAtom) atom).getArguments());
//		assert !mNegativelySetPoints.contains(point) : "is that ok??";
		if (mPositivelySetPoints.contains(point)) {
			return false;
		} else {
			mNegativelySetPoints.add(point);
			mPointToAtom.put(point, atom);
//			updateUnitClausesOnPointSetting(false, atom);
			updateClauseLiteralFulfillabilityOnPointSetting(false, point);
			return true;
		}
	}
	
	/**
	 * Called when a point is set.
	 * Checks for each epr-clause if it becomes a unit clause because of that. Updates that clause's status accordingly.
	 * @param settingPositive is true if this method was called because atom is being set positive, negative if atom is being
	 *  set negative
	 * @param atom
	 */
//	private void updateUnitClausesOnPointSetting(boolean settingPositive, EprPredicateAtom atom) {
	private void updateClauseLiteralFulfillabilityOnPointSetting(boolean settingPositive, TermTuple point) {
		for (Entry<EprClause, HashSet<Literal>> qo : mQuantifiedOccurences.entrySet()) {
			EprClause clause = qo.getKey();
			for (Literal li : qo.getValue()) {
				boolean oppositeSigns = li.getSign() == 1 ^ settingPositive;
				TermTuple otherPoint = new TermTuple(((EprPredicateAtom) li.getAtom()).getArguments());
				HashMap<TermVariable, ApplicationTerm> subs = point.match(otherPoint);
				if (oppositeSigns && subs != null) {
					clause.setLiteralUnfulfillable(li);
				}
			}
		}
		
	}

	public String toString() {
		return "EprPred: " + functionSymbol.getName();
	}

	public void unSetPointPositive(EprPredicateAtom atom) {
        TermTuple point = new TermTuple(((EprPredicateAtom) atom).getArguments());
		assert mPositivelySetPoints.contains(point) : "backtracking a point that was not set";
		mPointToAtom.remove(point);
		mPositivelySetPoints.remove(point);
	}
	
	public void unSetPointNegative(EprPredicateAtom atom) {
        TermTuple point = new TermTuple(((EprPredicateAtom) atom).getArguments());
		assert mNegativelySetPoints.contains(point) : "backtracking a point that was not set";
		mPointToAtom.remove(point);
		mNegativelySetPoints.remove(point);
	}

	/**
	 * Answers the question, if, 
	 *  - in the current decide state (communicated through setPoint-methods),
	 *  - given some excepted variables where we don't care (because of equalities in the clause),
	 *  - given a sign of the literal in which the predicate occurs in the current clause,
	 * this predicate is "true".
	 * Returns null if it is fulfilled, and a conflicting point if it is not.
	 * @param isLiteralPositive true, iff, the literal occurs positive in the clause
	 * @param literalSignature  the parameters of the literal's applicationTerm -- needed to see which are quantified and otherwise which constant is constrained
	 * @param exceptedConstants parameter positions to constants where we don't need to fulfill the predicate
	 */
	public TermTuple check(boolean isLiteralPositive, TermTuple literalSignature, HashMap<Integer,ArrayList<ApplicationTerm>> exceptedConstants) {
		HashSet<TermTuple> potentialConflictPoints = isLiteralPositive ?
				mNegativelySetPoints :
					mPositivelySetPoints;
		
		for (TermTuple tt : potentialConflictPoints) {
			if (literalSignature.matches(tt, exceptedConstants)) {
				//conflict!
				return tt;
			}
		}
		
		// no conflict
		return null;
	}
	
	public void addQuantifiedOccurence(Literal l, EprClause eprClause) {
		HashSet<Literal> val = mQuantifiedOccurences.get(eprClause);
		if (val == null) {
			val = new HashSet<>();
			mQuantifiedOccurences.put(eprClause, val);
		}
		val.add(l);
	}
	
	
	public EprPredicateAtom getAtomForPoint(TermTuple point) {
		return mPointToAtom.get(point);
	}
	
//	
//	public HashMap<EprClause,HashSet<Literal>> getQuantifiedOccurences() {
//		return mQuantifiedOccurences;
//	}

//	/**
//	 * Update the model such that atom is set.
//	 * This may return a conflict in form of a clause over almost-all atoms if the newly
//	 * set atom contradicts the current model.
//	 * (example: atom = <P v1 v2>, mAlmostAllAtoms = [(not <P v1 v1>)] will yield the conflict clause
//	 *  {(not <P v1 v2>), <P v1 v1>})
//	 * @param atom the almost-all atom that is to be set positively in the model
//	 * @param eprTheory 
//	 * @return conflict clause if there is a conflict with the current model, otherwise null
//	 */
//	public Clause setAlmostAllAtomPositive(EprAlmostAllAtom atom, EprTheory eprTheory) {
//		Clause conflict = null;
//
//		//update mPositiveAlmostAllAtoms
//		HashSet<EprAlmostAllAtom> alreadySetAtomsOfThisPredicate = mPositiveAlmostAllAtoms.get(atom.eprPredicate);
//		if (alreadySetAtomsOfThisPredicate == null) {
//			alreadySetAtomsOfThisPredicate = new HashSet<>();
//			mPositiveAlmostAllAtoms.put(atom.eprPredicate, alreadySetAtomsOfThisPredicate);
//		}
//		alreadySetAtomsOfThisPredicate.add(atom);
//		
//		//TODO: if this atom has already been set through closure, we ..?..
//
//
//		assert mNegativeAlmostAllAtoms.get(atom.eprPredicate) == null 
//				|| !mNegativeAlmostAllAtoms.get(atom.eprPredicate).contains(atom) : 
//					"DPLL sets that atom both positively and negatively? --> this cannot be, right?";
//
//		// check for conflicts with current model
//		if(mNegativeAlmostAllAtoms.get(atom.eprPredicate) != null) {
//			for (EprAlmostAllAtom aaa : mNegativeAlmostAllAtoms.get(atom.eprPredicate)) {
//				//case: setting <P ...>, already set (not <P ...>)
//				//			if (atom.signatureImplies(aaa)) {
//				if (atom.signature.implies(aaa.signature)) {
//					//case: setting <P x y>, already set (not <P x x>)
//					// conflict clause: {(not <P x y>), <P x x>}, i.e. <P x y> ==> <P x x>
//					return new Clause(new Literal[] { atom.negate(), aaa});
////					conflict = new Clause(new Literal[] { atom.negate(), aaa});
////					break;
//				}
//			}
//		}
//		
//		// add almost atoms that follow from the already set ones together with the one currently set
//		if(mPositiveAlmostAllAtoms.get(atom.eprPredicate) != null) {
//			//TODO do it efficiently
//			for (EprAlmostAllAtom aaa1 : mPositiveAlmostAllAtoms.get(atom.eprPredicate)) {
//				for (EprAlmostAllAtom aaa2 : mPositiveAlmostAllAtoms.get(atom.eprPredicate)) {
//					AAAtomSignature join = aaa1.signature.joinComplementary(aaa2.signature);
//					if (join != null) {
//						EprAlmostAllAtom newAtom = eprTheory.getEprAlmostAllAtom(
//								atom.getAssertionStackLevel(), atom.eprPredicate, join);
//						mPositiveAlmostAllAtoms.get(atom.eprPredicate).add(newAtom);
//						
//						HashSet<EprAlmostAllAtom> hs = mAAAtomsAddedThroughClosure.get(atom);
//						if (hs == null) {
//							hs = new HashSet<>();
//							mAAAtomsAddedThroughClosure.put(atom, hs);
//						}
//						hs.add(newAtom);
//					}
//				}
//			}
//		}
//
//		//no conflict detected
//		return null;
//	}
//
//	/**
//	 * Update the model such that atom is set.
//	 * This may return a conflict in form of a clause over almost-all atoms if the newly
//	 * set atom contradicts the current model.
//	 * @param atom the almost-all atom that is to be set negatively in the model
//	 * @param eprTheory 
//	 * @return conflict clause if there is a conflict with the current model, otherwise null
//	 */
//	public Clause setAlmostAllAtomNegative(EprAlmostAllAtom atom, EprTheory eprTheory) {
////		//(dual to positive case, of course)
////		mNegativeAlmostAllAtoms.add(atom);
////		assert !mPositiveAlmostAllAtoms.contains(atom) : 
////			"DPLL sets that atom both positively and negatively? --> this cannot be, right?";
////
////		//check for conflicts with current model
////		for (EprAlmostAllAtom aaa : mPositiveAlmostAllAtoms) {
////			//case: setting (not <P ...>), already set <P ...>
//////			if (atom.signatureImplies(aaa)) {
////			if (atom.signature.implies(aaa.signature)) {
////				//case: setting (not <P x y>), already set <P x x>
////				// conflict clause: { <P x y>, (not <P x x>)}, i.e. (not <P x y>) ==> (not <P x x>)
////				Literal[] lits = new Literal[2];
////				lits[0] = atom;
////				lits[1] = aaa.negate();
////				return new Clause(lits);
////			}
//////			if (aaa.signature.implies(atom.signature)) {
//////				Literal[] lits = new Literal[2];
//////				lits[0] = atom;
//////				lits[1] = aaa.negate();
//////				return new Clause(lits);
//////			}
////		}
//			
//		//no conflict detected
//		return null;
//
//	}
//
//	public void unSetAlmostAllAtomPositive(EprAlmostAllAtom atom) {
//		mPositiveAlmostAllAtoms.remove(atom);
//	}
//
//	public void unSetAlmostAllAtomNegative(EprAlmostAllAtom atom) {
//		mNegativeAlmostAllAtoms.remove(atom);
//	}
//	
////	/*
////	 * Special predicate that describes the value the current EPR predicate has at
////	 * almost all positions.
////	 */
////	DPLLAtom mAlmostAllAtom;
//////	EprPredicateAtom mAlmostAllAtom;
////
////	public DPLLAtom getAlmostAllAtom(Clausifier cl) {
////		if (mAlmostAllAtom == null) {
////			//TODO: is this the right way to introduce a literal??..
////			Term boolConst = cl.getTheory().constant("AA_" + mFunctionSymbol.toString(), cl.getTheory().getBooleanSort());
////			mAlmostAllAtom = cl.getCreateLiteral(boolConst).getAtom();
////		}
////		return mAlmostAllAtom;
////	}
}
