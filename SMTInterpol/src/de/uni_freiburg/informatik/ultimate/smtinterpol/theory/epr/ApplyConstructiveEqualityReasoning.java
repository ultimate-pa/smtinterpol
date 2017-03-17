package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprAtom;

/**
 * Given an epr clause (i.e. a clause with free variables), "Constructive equality reasoning" eliminates 
 * all literals that mention a variable at least twice by introducing disequalities into the clause.
 * 
 * Examples:
 *  The clause { P x x } is transformed to { x != x', P x x' }
 *  The clause { A, B, Q x x c y x } is transformed to { A, B x, x != x', x != x'', Q x x' c y x'' } 
 *    (introducing two disequalities should be enough here for the clause to be equivalent)
 * 
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
class ApplyConstructiveEqualityReasoning {
	
	final EprTheory mEprTheory;
	final Set<Literal> mResult;

	public ApplyConstructiveEqualityReasoning(EprTheory eprTheory, Set<Literal> inputLiterals) {
		mEprTheory = eprTheory;
		
		final Set<Literal> newLiterals = new HashSet<Literal>();
		
		for (Literal inputLit : inputLiterals) {
			
			// this -should- always be an ApplicationTerm, right?
			final ApplicationTerm atomFormula = 
					(ApplicationTerm) inputLit.getAtom().getSMTFormula(mEprTheory.getTheory()); 
			
			final BinaryRelation<TermVariable, Integer> variableOccurences = 
					getOccurrences(atomFormula.getParameters());
			
			final Map<Integer, TermVariable> positionToNewTv = new HashMap<Integer, TermVariable>();
			
			for (TermVariable tv : variableOccurences.getDomain()) {

				final Set<Integer> occurences = variableOccurences.getImage(tv);

				final Integer firstOccurrence = occurences.iterator().next();
				positionToNewTv.put(firstOccurrence, tv);

				final HashSet<Integer> otherOccurrences = new HashSet<Integer>(occurences);
				otherOccurrences.remove(firstOccurrence);
				
				/*
				 * for each "other" occurence of the current TermVariable 
				 *   (i.e., occurence that is not the first one),
				 *  - create a fresh TermVariable
				 *  - add a disequality literal
				 *  - update the map from position to new TermVariables
				 */
				for (Integer otherOc : otherOccurrences) {
					final TermVariable freshTv = 
							mEprTheory.getTheory().createFreshTermVariable("CER", tv.getSort());

					// create the equality (= tv freshTv) and add its negated literal to the new clause
					final ApplicationTerm newEquality = mEprTheory.getTheory().term("=", tv, freshTv);
					newLiterals.add(
							mEprTheory.getEprAtom(newEquality, 
									0,  //TODO hash
									mEprTheory.getClausifier().getStackLevel()).negate());
					
					positionToNewTv.put(otherOc, freshTv);
				}
			}
			
			/*
			 * compute a new parameters-array
			 */
			final Term[] newParameters = new Term[atomFormula.getParameters().length];
			for (int i = 0; i < newParameters.length; i++) {
				newParameters[i] = atomFormula.getParameters()[i] instanceof ApplicationTerm ?
						atomFormula.getParameters()[i] :
							positionToNewTv.get(i);
				assert newParameters[i] != null;
			}
			
			/*
			 * construct the new literal and add it to the resulting clause/literal set
			 */
			final ApplicationTerm newTerm = mEprTheory.getTheory().term(atomFormula.getFunction(), newParameters);
			final EprAtom newAtom = mEprTheory.getEprAtom(newTerm, 
					0, 
					mEprTheory.getClausifier().getStackLevel());
			newLiterals.add(inputLit.getSign() == 1 ? newAtom : newAtom.negate());
			
		}
		
		mResult = newLiterals;
	}

	/**
	 * Maps each TermVariable occuring in parameters to all indices of the array it occurs at.
	 * 
	 * @param parameters
	 * @return
	 */
	private BinaryRelation<TermVariable, Integer> getOccurrences(Term[] parameters) {
		final BinaryRelation<TermVariable, Integer> result = new BinaryRelation<TermVariable, Integer>();
		for (int i = 0; i < parameters.length; i++) {
			if (parameters[i] instanceof TermVariable) {
				result.addPair((TermVariable) parameters[i], i);
			}
		}
		return result;
	}
	
	public Set<Literal> getResult() {
		return mResult;
	}

}
