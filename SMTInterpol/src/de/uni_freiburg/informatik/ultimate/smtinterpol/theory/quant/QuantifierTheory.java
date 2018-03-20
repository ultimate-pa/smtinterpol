/*
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;

/**
 * Solver for quantified formulas within the almost uninterpreted fragment (Restrictions on terms and literals are
 * explained in the corresponding classes. For reference, see Ge & de Moura, 2009).
 * 
 * This may be merged with the EPR solver implementation by Alexander Nutz in the future; for now, we keep it separate.
 *
 * @author Tanja Schindler
 *
 */
public class QuantifierTheory implements ITheory {

	private Clausifier mClausifier;
	private final LogProxy mLogger;
	private Theory mTheory;
	private DPLLEngine mEngine;

	private EUTermManager mTermManager;
	private QuantLiteralManager mLitManager;

	/**
	 * Clauses that only the QuantifierTheory knows, i.e. that contain at least one literal with an (implicitly)
	 * universally quantified variable.
	 */
	private Set<QuantClause> mQuantClauses;
	/**
	 * For each variable, the set of potentially interesting instantiations.
	 */
	private Map<TermVariable, Set<Term>> mInstantiationTerms;

	public QuantifierTheory(final Theory th, final DPLLEngine engine, final Clausifier clausifier) {
		mClausifier = clausifier;
		mLogger = clausifier.getLogger();
		mTheory = th;
		mEngine = engine;

		mTermManager = new EUTermManager(this);
		mLitManager = new QuantLiteralManager(this);

		mQuantClauses = new HashSet<QuantClause>();
	}

	@Override
	public Clause startCheck() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void endCheck() {
		// TODO Auto-generated method stub

	}

	@Override
	public Clause setLiteral(Literal literal) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void backtrackLiteral(Literal literal) {
		// TODO Auto-generated method stub

	}

	@Override
	public Clause checkpoint() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Clause computeConflictClause() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Literal getPropagatedLiteral() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Clause getUnitClause(Literal literal) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Literal getSuggestion() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void printStatistics(LogProxy logger) {
		// TODO Auto-generated method stub

	}

	@Override
	public void dumpModel(LogProxy logger) {
		// TODO Auto-generated method stub

	}

	@Override
	public void increasedDecideLevel(int currentDecideLevel) {
		// TODO Auto-generated method stub

	}

	@Override
	public void decreasedDecideLevel(int currentDecideLevel) {
		// TODO Auto-generated method stub

	}

	@Override
	public Clause backtrackComplete() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void restart(int iteration) {
		// TODO Auto-generated method stub

	}

	@Override
	public void removeAtom(DPLLAtom atom) {
		// TODO Auto-generated method stub

	}

	@Override
	public Object push() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void pop(Object object, int targetlevel) {
		// TODO Auto-generated method stub

	}

	@Override
	public Object[] getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void fillInModel(Model model, Theory t, SharedTermEvaluator ste) {
		// TODO Auto-generated method stub

	}

	/**
	 * Get a quantified equality atom for a term - in case the <em>literal</em> is supported. We support the literals
	 * "EUTerm = EUTerm" (pos. and neg.), "TermVariable = GroundTerm" (pos. and neg.) and "TermVariable != TermVariable"
	 * (only negated!).
	 * <p>
	 * Note that this returns the underlying <em>atom</em>. The Clausifier will negate it if the original term in the
	 * clause was negated.
	 * 
	 * @param positive
	 *            flag that indicates if the term is positive or negated. This is required to determine if the literal
	 *            is supported.
	 * @param term
	 *            the term for the underlying equality atom.
	 * @param source
	 *            the source partition of the term.
	 * @param lhs
	 *            the term at the left hand side of the equality.
	 * @param rhs
	 *            the term at the right hand side of the equality.
	 * @return the underlying equality atom as a QuantLiteral, if the literal is supported.
	 */
	public QuantLiteral getQuantEquality(boolean positive, Term term, SourceAnnotation source, Term lhs, Term rhs) {
		return mLitManager.getQuantEquality(positive, term, source, lhs, rhs);
	}

	/**
	 * Get a quantified inequality atom for a term - in case the <em>literal</em> is supported. We support the literals
	 * "EUTerm <= 0" (pos. or neg.), or (only strict inequalities, i.e. negated) "TermVariable < GroundTerm",
	 * "GroundTerm < TermVariable", "TermVariable < TermVariable"
	 * <p>
	 * Note that this returns the underlying <em>atom</em>. The Clausifier will negate it if the original term in the
	 * clause was negated.
	 * 
	 * @param positive
	 *            flag that indicates if the term is positive or negated. This is required to determine if the literal
	 *            is supported.
	 * @param term
	 *            the term for the underlying inequality atom "term <= 0".
	 * @param source
	 *            the source partition of the term.
	 * @param lhs
	 *            the left hand side in "term <= 0"
	 * @return the underlying inequality atom as a QuantLiteral, if the literal is supported.
	 */
	public QuantLiteral getQuantInequality(boolean positive, Term term, SourceAnnotation source, Term lhs) {
		return mLitManager.getQuantInequality(positive, term, source, lhs);
	}

	public QuantLiteral getQuantNamedAtom(Term term) {
		return new QuantNamedAtom(term); // TODO Should this be in QuantLiteralManager, too?
	}

	/**
	 * Add a QuantClause for a given set of literals and quantified literals.
	 *
	 * This should be called after applying DER.
	 *
	 * @param lits
	 *            ground literals in the new clause.
	 * @param quantLits
	 *            literals in the new clause containing at least one free variable.
	 * @param hook
	 * @param proof
	 */
	public void addQuantClause(final Literal[] lits, final QuantLiteral[] quantLits, final ClauseDeletionHook hook,
			final ProofNode proof) {
		assert quantLits.length != 0 : "Adding QuantClause without QuantLit!";
		final QuantClause clause = new QuantClause(lits, quantLits, this);
		clause.collectVarInfo();
		mQuantClauses.add(clause);
		// TODO
		throw new UnsupportedOperationException("Support for quantifiers coming soon.");
	}

	/**
	 * Get all EUTerms that are sub-terms of a given term.
	 * 
	 * @param euTerm
	 *            the EUTerm we want to get the subterms for.
	 * @return a set of EUTerms containing all sub-EUTerms of a term, including the term itself.
	 */
	public Set<EUTerm> getSubEUTerms(EUTerm euTerm) {
		return mTermManager.getSubEUTerms(euTerm);
	}

	public Clausifier getClausifier() {
		return mClausifier;
	}

	public EUTermManager getEUTermManager() {
		return mTermManager;
	}
}
