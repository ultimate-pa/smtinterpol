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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinArSolve;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

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

	private final Clausifier mClausifier;
	private final LogProxy mLogger;
	private final Theory mTheory;
	private final DPLLEngine mEngine;

	final CClosure mCClosure;
	final LinArSolve mLinArSolve;

	private final EUTermManager mTermManager;
	private final QuantLiteralManager mLitManager;

	/**
	 * Clauses that only the QuantifierTheory knows, i.e. that contain at least one literal with an (implicitly)
	 * universally quantified variable.
	 */
	private ScopedHashSet<QuantClause> mQuantClauses;

	public QuantifierTheory(final Theory th, final DPLLEngine engine, final Clausifier clausifier) {
		mClausifier = clausifier;
		mLogger = clausifier.getLogger();
		mTheory = th;
		mEngine = engine;

		mCClosure = clausifier.getCClosure();
		mLinArSolve = clausifier.getLASolver();

		mTermManager = new EUTermManager(this);
		mLitManager = new QuantLiteralManager(this);

		mQuantClauses = new ScopedHashSet<QuantClause>();
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
		for (final QuantClause clause : mQuantClauses) {
			// TODO Each clause should check if this literal leads to a conflicting instance
		}
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void backtrackLiteral(Literal literal) {
		// TODO Auto-generated method stub

	}

	@Override
	public Clause checkpoint() {
		for (final QuantClause clause : mQuantClauses) {
			// Each clause should update the potential instantiations
			clause.computeInstantiationTerms();
			// TODO and instantiate conflict or unit clauses
		}
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Clause computeConflictClause() {
		// TODO Auto-generated method stub
		// TODO For each clause, compute all instantiations.
		throw new UnsupportedOperationException("Support for quantifiers coming soon.");
	}

	@Override
	public Literal getPropagatedLiteral() {
		// Nothing to do
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
		mQuantClauses.beginScope();
		for (final QuantClause qClause : mQuantClauses) {
			qClause.push();
		}
		return null;
	}

	@Override
	public void pop(Object object, int targetlevel) {
		mQuantClauses.endScope();
		for (final QuantClause qClause : mQuantClauses) {
			qClause.pop();
		}

	}

	@Override
	public Object[] getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * Get a quantified equality atom for a term - in case the <em>literal</em> is supported. We support the literals
	 * "EUTerm = EUTerm" (pos. and neg.), "TermVariable = GroundTerm" (pos. and neg.) and "TermVariable != TermVariable"
	 * (only negated!).
	 * <p>
	 * Note that this returns the underlying <em>atom</em>. The Clausifier will negate it if the original term in the
	 * clause was negated.
	 * 
	 * @param term
	 *            the term for the underlying equality atom.
	 * @param positive
	 *            flag that indicates if the term appears positively or negated in the clause. This is required to
	 *            determine if the literal is supported.
	 * @param source
	 *            the source partition of the term.
	 * @param lhs
	 *            the term at the left hand side of the equality.
	 * @param rhs
	 *            the term at the right hand side of the equality.
	 * 
	 * @return the underlying equality atom as a QuantLiteral, if the literal is supported.
	 */
	public QuantLiteral getQuantEquality(Term term, boolean positive, SourceAnnotation source, Term lhs, Term rhs) {
		return mLitManager.getQuantEquality(term, positive, source, lhs, rhs);
	}

	/**
	 * Get a quantified inequality literal for a term - in case it is supported. We support the literals "EUTerm <= 0"
	 * (pos. or neg.), or (only strict inequalities, i.e., negated non-strict inequalities) "not (TermVariable <=
	 * GroundTerm)", "not (GroundTerm <= TermVariable)", "not (TermVariable <= TermVariable)"
	 * <p>
	 * Note that this will return a <em>negated</em> literal (not (x<=t)) in the latter three cases if positive==true!
	 * 
	 * @param term
	 *            the term for the underlying inequality <em>atom</em> "term <= 0".
	 * @param positive
	 *            flag that indicates if the term appears positively or negated in the clause. This is required to
	 *            determine if the literal is supported.
	 * @param source
	 *            the source partition of the term.
	 * @param lhs
	 *            the left hand side in "term <= 0"
	 * 
	 * @return a QuantLiteral if the literal is supported.
	 */
	public QuantLiteral getQuantInequality(Term term, boolean positive, SourceAnnotation source, Term lhs) {
		return mLitManager.getQuantInequality(term, positive, source, lhs);
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
