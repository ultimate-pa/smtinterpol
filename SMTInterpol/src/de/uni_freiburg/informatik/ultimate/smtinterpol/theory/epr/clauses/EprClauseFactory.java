/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.ApplyConstructiveEqualityReasoning;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
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
	public EprClause createResolvent(ClauseEprLiteral pivot1, ClauseEprLiteral pivot2) {
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
		

		// apply the unifier to the literals of c1 and c2, add the unified literals to the resolvent
		Set<Literal> resLits = computeUnifiedLiteralsFromClauseLiterals(unifier, resCls);
	

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
		
		final Set<Literal> resLits = computeUnifiedLiteralsFromClauseLiterals(unifier, resCls);

//		assert getEprClause(resLits).isConflict(); //TODO: does the side effect hurt??

		final Set<Literal> cerResLits = new ApplyConstructiveEqualityReasoning(mEprTheory, resLits).getResult();
		
		final EprClause factor = getEprClause(cerResLits);

//		 weakened the following assertion by the left disjunct, because CER may make the conflict "non-obvious"..
//		assert !cerResLits.equals(resLits) || factor.isConflict();
		assert factor.isConflict();

		mEprTheory.getStateManager().learnClause(factor);
		return factor;
	}

	/**
	 * Makes sure that for the same set of literals only one clause is constructed.
	 * Also applies alpha renaming such that the free variables of every newly created EprClause
	 * are not used by any other EprClause (necessary to obtain the -most general- unifier for first-
	 * order resolution).
	 * 
	 * TODO: it would be even better if instead of "same set of literals" the criterion would be
	 *    "same set of literals modulo alpha renaming".
	 */
	public EprClause getEprClause(Set<Literal> literals) {
		
		Set<Literal> alphaRenamedLiterals = alphaRenameLiterals(literals);
		
		EprClause result = mLiteralsToClause.get(alphaRenamedLiterals);
		if (result == null) {
			result = new EprClause(alphaRenamedLiterals, mEprTheory);
			mEprTheory.getLogger().debug("EPRDEBUG (EprClauseFactory): creating new clause " + result);
			mLiteralsToClause.put(alphaRenamedLiterals, result);
		} else {
			mEprTheory.getLogger().debug("EPRDEBUG (EprClauseFactory): clause has been added before " + result);
			result.mClauseStateIsDirty = true;
		}
		return result;
	}

	public void push() {
		mLiteralsToClause.beginScope();
	}
	
	public void pop() {
		mLiteralsToClause.endScope();
	}

	private Set<Literal> computeUnifiedLiteralsFromClauseLiterals(TTSubstitution unifier, Set<ClauseLiteral> resCls) {
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
	
	/**
	 * Applies alpha renaming to a set of literals assuming they will form one clause.
	 *  --> keeps one substitution that is applied to all literals and updated when a new
	 *    free variable is encountered.
	 * @param literals
	 * @return
	 */
	private Set<Literal> alphaRenameLiterals(Set<Literal> literals) {
		Set<Literal> alphaRenamedLiterals = new HashSet<Literal>();
		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
		for (Literal l : literals) {
			if (l.getAtom() instanceof EprQuantifiedEqualityAtom 
					|| l.getAtom() instanceof EprQuantifiedPredicateAtom) {
				EprAtom arAtom = applyAlphaRenamingToQuantifiedEprAtom((EprAtom) l.getAtom(), substitution);
				Literal arLiteral = l.getSign() == 1 ? arAtom : arAtom.negate();
				alphaRenamedLiterals.add(arLiteral);
			} else {
				alphaRenamedLiterals.add(l);
			}
		}
		return alphaRenamedLiterals;
	}

	private EprAtom applyAlphaRenamingToQuantifiedEprAtom(EprAtom atom, Map<TermVariable, Term> sub) {
		assert atom instanceof EprQuantifiedPredicateAtom || atom instanceof EprQuantifiedEqualityAtom;

		for (Term t : atom.getArguments()) {
			if ((t instanceof ApplicationTerm) || sub.containsKey(t)) {
				continue;
			}
			TermVariable tv = (TermVariable) t;
			String newTvNamePrefix = tv.getName();
			// createFreshTermvariable adds a "." in front and something like ".123" after the given prefix
			//  --> after some iterations this becomes long, so we trim a little
			newTvNamePrefix = newTvNamePrefix.replaceAll("\\.\\d+", "");
			newTvNamePrefix = newTvNamePrefix.replaceAll("\\.(\\.)+", "");
			sub.put(tv, mEprTheory.getTheory().createFreshTermVariable(newTvNamePrefix, tv.getSort()));
		}

		TermTuple tt = atom.getArgumentsAsTermTuple();
		TermTuple ttSub = tt.applySubstitution(sub);
		FunctionSymbol fs = ((ApplicationTerm) atom.getSMTFormula(mEprTheory.getTheory())).getFunction();
		ApplicationTerm subTerm = mEprTheory.getTheory().term(fs, ttSub.terms);
		EprAtom subAtom = mEprTheory.getEprAtom(subTerm, 0, mEprTheory.getClausifier().getStackLevel()); //TODO hash
		return subAtom;
	}
}
