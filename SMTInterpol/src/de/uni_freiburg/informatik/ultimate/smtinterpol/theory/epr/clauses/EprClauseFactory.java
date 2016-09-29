package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * 
 * @author Alexander Nutz
 */
public class EprClauseFactory {
	
	EprTheory mEprTheory;
	
	/**
	 * Remembers from which sets of literals an EprClause has already been 
	 * constructed (and which).
	 */
	private ScopedHashMap<Set<Literal>, EprClause> mLiteralsToClause = new ScopedHashMap<Set<Literal>, EprClause>();
	
	public EprClauseFactory(EprTheory eprTheory) {
		mEprTheory = eprTheory;
	}
		
	/**
	 * 
	 * @param pivot1 A ClauseLiteral of c1, the pivot on the side of c1, 
	 *              pivot1 is necessarily a quantified epr literal, because it comes from the epr decide stack
	 * @param pivot2 A ClauseLiteral that was used for propagation, 
	 *          its clause is the other clause for the resolution, the parameter is the pivot on that side
	 *           pivot2 is an epr literal that contradicts pivot1, it may be ground
	 * @return the resolvent of pivot1.getEprClause and pivot1.getEprClause with pivot1 and pivot2 as pivots
	 */
	public EprClause createResolvent(ClauseEprQuantifiedLiteral pivot1, ClauseEprLiteral pivot2) {
		assert pivot1.getPolarity() != pivot2.getPolarity();
		
		int arity = pivot1.getArguments().size();
		assert arity == pivot2.getArguments().size();
		
		EprClause c1 = pivot1.getClause();
		EprClause c2 = pivot2.getClause();
		
		Set<ClauseLiteral> c1Lits = c1.getLiterals();
		Set<ClauseLiteral> c2Lits = c2.getLiterals();
		
		TermTuple p1tt = new TermTuple(pivot1.getArguments().toArray(new Term[arity]));
		TermTuple p2tt = new TermTuple(pivot2.getArguments().toArray(new Term[arity]));
		TTSubstitution unifier = p1tt.match(p2tt, mEprTheory.getEqualityManager());

		Set<ClauseLiteral> resCls = new HashSet<ClauseLiteral>();
		resCls.addAll(c1Lits);
		resCls.remove(pivot1);
		resCls.addAll(c2Lits);
		resCls.remove(pivot2);
		
		String alphaRenamingIdentifier = new String("alpha renaming for resolvent of clausese" 
				+ c1 + " and " + c2 + "with pivot" + pivot1);
		mEprTheory.notifyAboutNewClause(alphaRenamingIdentifier);

		// apply the unifier to the literals of c1 and c2, add the unified literals to the resolvent
		Set<Literal> resLits = computeUnifiedLiteralsFromClauseLiterals(unifier, resCls, alphaRenamingIdentifier);
	

		EprClause resolvent = getEprClause(resLits);

		mEprTheory.getStateManager().learnClause(resolvent);
		
		return resolvent;
	}
	
	public EprClause getFactoredClause(ClauseEprQuantifiedLiteral factorLit1, ClauseEprLiteral factorLit2) {
		assert factorLit1.getPolarity() == factorLit2.getPolarity();
		
		EprPredicate flPred = factorLit1.getEprPredicate();
		assert flPred == factorLit2.getEprPredicate();
		assert factorLit1.getClause() == factorLit2.getClause();
		int arity = flPred.getArity();
		
		EprClause clause = factorLit1.getClause();
		
		Set<ClauseLiteral> cLits = clause.getLiterals();
		
		TermTuple p1tt = new TermTuple(factorLit1.getArguments().toArray(new Term[arity]));
		TermTuple p2tt = new TermTuple(factorLit2.getArguments().toArray(new Term[arity]));
		TTSubstitution unifier = p1tt.match(p2tt, mEprTheory.getEqualityManager());
		
		
		Set<ClauseLiteral> resCls = new HashSet<ClauseLiteral>();
		resCls.addAll(cLits);
		resCls.remove(factorLit2);
		
		String alphaRenamingIdentifier = new String("alpha renaming for factoring of clause" 
				+ clause + " with " + factorLit1 + " and " + factorLit2);
		mEprTheory.notifyAboutNewClause(alphaRenamingIdentifier);
	
		Set<Literal> resLits = computeUnifiedLiteralsFromClauseLiterals(unifier, resCls, alphaRenamingIdentifier);
		
		EprClause factor = getEprClause(resLits);
		mEprTheory.getStateManager().learnClause(factor);
		return factor;
	}

	/**
	 * makes sure that for the same set of literals only one clause is constructed.
	 * Note that this may return a EprDerivedClause -- if there already is one for the set of Literals
	 * (copy from the old getBaseClause method)
	 */
	public EprClause getEprClause(Set<Literal> newLits) {
		EprClause result = mLiteralsToClause.get(newLits);
		if (result == null) {
			result = new EprClause(newLits, mEprTheory);
			mEprTheory.getLogger().debug("EPRDEBUG (EprClauseFactory): creating new clause " + result);
			mLiteralsToClause.put(newLits, result);
		} else {
			mEprTheory.getLogger().debug("EPRDEBUG (EprClauseFactory): clause has been added before " + result);
		}
		return result;
	}
	
	public void push() {
		mLiteralsToClause.beginScope();
	}
	
	public void pop() {
		mLiteralsToClause.endScope();
	}

	private Set<Literal> computeUnifiedLiteralsFromClauseLiterals(TTSubstitution unifier, Set<ClauseLiteral> resCls,
			String alphaRenamingIdentifier) {
		// apply the unifier to the literals of c1 and c2, add the unified literals to the resolvent
		Set<Literal> resLits = new HashSet<Literal>();
		for (ClauseLiteral cl : resCls) {

			if (cl instanceof ClauseEprQuantifiedLiteral) {
				ClauseEprQuantifiedLiteral clQ = (ClauseEprQuantifiedLiteral) cl;
				EprPredicate pred = clQ.getEprPredicate();
				List<Term> clArgs = clQ.getArguments();
				TermTuple cltt = new TermTuple(clArgs.toArray(new Term[clArgs.size()]));
				TermTuple unifiedClTt = unifier.apply(cltt);
				
				Literal newCl = null;
				if (unifiedClTt.isGround()) {
					EprGroundPredicateAtom atom = (EprGroundPredicateAtom) pred.getAtomForTermTuple(
							unifiedClTt, mEprTheory.getTheory(), mEprTheory.getClausifier().getStackLevel());
					newCl = cl.getPolarity() ? atom : atom.negate();
				} else {

					EprQuantifiedPredicateAtom atom = (EprQuantifiedPredicateAtom) 
							pred.getAtomForTermTuple(unifiedClTt, 
									mEprTheory.getTheory(), 
									mEprTheory.getClausifier().getStackLevel());
					
					// apply alpha renaming
					atom = (EprQuantifiedPredicateAtom) mEprTheory.getEprAtom(
							(ApplicationTerm) atom.getSMTFormula(mEprTheory.getTheory()), 
							0, mEprTheory.getClausifier().getStackLevel(), alphaRenamingIdentifier);
					
					newCl = cl.getPolarity() ? atom : atom.negate();
				}
				resLits.add(newCl);
			} else {
				//TODO: should we still handle equalities by allowing the unifier to also replace constants?
				// --> in that case we need to check ground literals, too..
				resLits.add(cl.getLiteral());
			}
		}
		return resLits;
	}
}
