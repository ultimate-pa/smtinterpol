package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.IEprLiteral;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

public class EprClauseManager {
	
	private final ScopedHashSet<EprClause> mEprClauses = new ScopedHashSet<EprClause>();

	/**
	 * Remembers for each DPLLAtom in which EprClauses it occurs (if any).
	 */
	ScopedHashMap<DPLLAtom, HashSet<EprClause>> mDPLLAtomToClauses = 
			new ScopedHashMap<DPLLAtom, HashSet<EprClause>>();

	private EprTheory mEprTheory;
	
	public EprClauseManager(EprTheory eprTheory) {
		mEprTheory = eprTheory;
	}
	
	public void push() {
		mEprClauses.beginScope();
		mDPLLAtomToClauses.beginScope();
	}
	
	public void pop() {
		for (EprClause ec : mEprClauses.currentScope()) {
			ec.disposeOfClause();
		}
		mEprClauses.endScope();
		mDPLLAtomToClauses.endScope();
	}

	public void addClause(EprClause newClause) {
		mEprClauses.add(newClause);
	}

	public Iterable<EprClause> getAllClauses() {
		return mEprClauses;
	}
	
	/**
	 * Ask the clauses what happens if dcideStackQuantifiedLiteral is set.
	 * Returns a conflict that the setting of the literal would induce, null if there is none.
	 * 
	 * @param literalToBeSet
	 * @return an EprClause that is Unit or Conflict if there is one, null otherwise
	 */
	public Set<EprClause> updateClausesOnSetEprLiteral(IEprLiteral literalToBeSet) {
		
		HashMap<EprClause, HashSet<ClauseEprLiteral>> allOccurences = 
				literalToBeSet.getEprPredicate().getAllEprClauseOccurences();
		
		Set<EprClause> unitClauses = new HashSet<EprClause>();
	
		for (Entry<EprClause, HashSet<ClauseEprLiteral>> en : allOccurences.entrySet()) {
			EprClause eprClause = en.getKey();
			
			eprClause.updateStateWrtDecideStackLiteral(literalToBeSet, en.getValue());

			if (eprClause.isConflict()) {
				return new HashSet<EprClause>(Collections.singleton(eprClause));
			} else if (eprClause.isUnit()) {
				unitClauses.add(eprClause);
			}
		}
		
		if (! unitClauses.isEmpty()) {
			return unitClauses;
		}

		return null;
	}

	/**
	 * this -might- be unnecessary
	 *   -- depending on whether the clauses look at the decide stack themselves anyway..
	 *     --> still unclear.. (TODO)
	 * @param dsl
	 */
	void updateClausesOnBacktrackDecideStackLiteral(DecideStackLiteral dsl) {
		HashMap<EprClause, HashSet<ClauseEprLiteral>> allOccurences = 
				dsl.getEprPredicate().getAllEprClauseOccurences();
		
		for (Entry<EprClause, HashSet<ClauseEprLiteral>> en : allOccurences.entrySet()) {
			EprClause eprClause = en.getKey();
			
			eprClause.backtrackStateWrtDecideStackLiteral(dsl);
		}
	}

	/**
	 * Inform all the EprClauses that contain the atom (not only the
	 * literal!) that they have to update their fulfillment state.
	 * 
	 * Note: This is not enough for EprGroundAtoms because they might interfere with 
	 * quantified literals which don't have the same atom..
	 */
	public Set<EprClause> updateClausesOnSetDpllLiteral(Literal literal) {
		HashSet<EprClause> clauses = 
				this.mDPLLAtomToClauses.get(literal.getAtom());
		if (clauses == null) {
			return null;
		}

		Set<EprClause> unitClauses = new HashSet<EprClause>();
		for (EprClause ec : clauses) {
			EprClauseState newClauseState = 
					ec.updateStateWrtDpllLiteral(literal);

			if (newClauseState == EprClauseState.Conflict) {
				return Collections.singleton(ec);
			} else if (newClauseState == EprClauseState.Unit) {
				unitClauses.add(ec);
			}
		}
		
		if (! unitClauses.isEmpty()) {
			return unitClauses;
		}
		return null;
	}

	/**
	 * Informs the clauses that contain the literal's atom that
	 * it is backtracked by the DPLLEngine.
	 * @param literal
	 */
	public void updateClausesOnBacktrackDpllLiteral(Literal literal) {
		HashSet<EprClause> clauses = 
				this.mDPLLAtomToClauses.get(literal.getAtom());
		if (clauses != null) {
			for (EprClause ec : clauses) {
				ec.backtrackStateWrtDpllLiteral(literal);
			}
		}
	}

	public void updateAtomToClauses(DPLLAtom atom, EprClause c) {
		HashSet<EprClause> clauses = mDPLLAtomToClauses.get(atom);
		if (clauses == null) {
			clauses = new HashSet<EprClause>();
			mDPLLAtomToClauses.put(atom, clauses);
		}
		clauses.add(c);
	}

	/**
	 * Add a clause coming from the input script.
	 * @return A ground conflict if adding the given clause directly leads to one.
	 */
	public Clause createEprClause(HashSet<Literal> literals) {
		EprClause newClause = mEprTheory.getEprClauseFactory().getEprClause(literals);
		
		return registerEprClause(newClause);
	}

	/**
	 * Register an eprClause (coming from input or learned) in the corresponding places...
	 * 
	 * Check if it is unit or a conflict.
	 * If it is a conflict immediately resolve it (on the epr decide stack) and return a ground conflict
	 * if the conflict is not resolvable.
	 * If it is unit, queue it for propagation.
	 */
	public Clause registerEprClause(EprClause newClause) {
		addClause(newClause);

		for (ClauseLiteral cl : newClause.getLiterals()) {
			updateAtomToClauses(cl.getLiteral().getAtom(), newClause);
		}
		return mEprTheory.getStateManager().getDecideStackManager()
				.resolveConflictOrStoreUnits(new HashSet<EprClause>(Collections.singleton(newClause)));
	}
}
