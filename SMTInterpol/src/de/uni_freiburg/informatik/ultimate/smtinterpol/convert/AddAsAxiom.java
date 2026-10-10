/*
 * Copyright (C) 2009-2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;

class AddAsAxiom implements Operation {
	/**
	 *
	 */
	final Clausifier clausifier;
	/**
	 * The term to add as axiom. This is annotated with its proof.
	 */
	final Term mAxiom;
	/**
	 * The source node.
	 */
	private final SourceAnnotation mSource;

	/**
	 * The sat-proof record proving {@code provedTerm(mAxiom)} as a positive proof
	 * literal, filled in once this node -- and, for a propositional split, its
	 * {@link SplitJoin} -- has run. Stays null when sat proofs are disabled, or
	 * when this node's derivation isn't (yet) tracked, e.g. quantified formulas
	 * (see the model-proof plan, phase 4) or a formula that turned out to already
	 * be asserted; the caller then falls back to evaluating the formula directly
	 * instead of using this record.
	 */
	Clausifier.SatRecord mSatProof;

	/**
	 * Add the clauses for an asserted term.
	 *
	 * @param axiom
	 *            the term to assert annotated with the proof for the corresponding unit clause.
	 * @param source
	 *            the prepared proof node containing the source annotation.
	 * @param clausifier TODO
	 */
	public AddAsAxiom(Clausifier clausifier, final Term axiom, final SourceAnnotation source) {
		this.clausifier = clausifier;
		assert axiom.getSort().getName() == "Bool";
		mAxiom = axiom;
		mSource = source;
	}

	/** Record a leaf clause's sat-proof record (target {provedTerm(mAxiom)}) as this node's own. */
	private void setLeafSatProof(final Clausifier.ClauseSatProof csp) {
		mSatProof = csp;
	}

	@Override
	public void perform() {
		Term term = this.clausifier.mTracker.getProvedTerm(mAxiom);
		boolean positive = true;
		while (Clausifier.isNotTerm(term)) {
			term = Clausifier.toPositive(term);
			positive = !positive;
		}
		final int oldFlags = this.clausifier.getTermFlags(term);
		int assertedFlag, auxFlag;
		if (positive) {
			assertedFlag = Clausifier.POS_AXIOMS_ADDED;
			auxFlag = Clausifier.POS_AUX_AXIOMS_ADDED;
		} else {
			assertedFlag = Clausifier.NEG_AXIOMS_ADDED;
			auxFlag = Clausifier.NEG_AUX_AXIOMS_ADDED;
		}
		if ((oldFlags & assertedFlag) != 0) {
			// We've already added this formula as axioms
			return;
		}
		// Mark the formula as asserted.
		// Also mark the auxFlag, as it is no longer necessary to create the auxiliary axioms that state that auxlit
		// implies this formula.
		this.clausifier.setTermFlags(term, oldFlags | assertedFlag);
		final ILiteral auxlit = this.clausifier.getILiteral(term);
		if (auxlit != null) {
			// add the unit aux literal as clause; this will basically make the auxaxioms the axioms after unit
			// propagation and level 0 resolution.
			if ((oldFlags & auxFlag) == 0) {
				this.clausifier.addAuxAxioms(term, positive, mSource);
			}
			setLeafSatProof(this.clausifier.buildClause(mAxiom, mSource));
			return;
		}
		final Theory t = mAxiom.getTheory();
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm at = (ApplicationTerm) term;
			if (!positive && at.getFunction() == t.mOr) {
				// the axioms added below already imply the auxaxiom clauses.
				this.clausifier.setTermFlags(term, oldFlags | assertedFlag | auxFlag);
				// A negated or is an and of negated formulas. Hence assert all negated
				// subformulas.
				final Term[] params = at.getParameters();
				final AddAsAxiom[] children = new AddAsAxiom[params.length];
				for (int i = 0; i < params.length; i++) {
					final Term p = params[i];
					final Term split =
							this.clausifier.mTracker.resolveBinaryTautology(mAxiom, t.term("not", p), ProofConstants.TAUT_OR_POS);
					children[i] = new AddAsAxiom(this.clausifier, split, mSource);
				}
				if (this.clausifier.satProofsEnabled()) {
					// or- {~term, p_1, .., p_k}, resolved with the children's (not p_i)
					final Term[] startLits = new Term[params.length + 1];
					startLits[0] = t.term("not", term);
					System.arraycopy(params, 0, startLits, 1, params.length);
					this.clausifier.pushOperation(new SplitJoin(this, children, startLits, ProofConstants.TAUT_OR_NEG));
				}
				for (int i = params.length - 1; i >= 0; i--) {
					this.clausifier.pushOperation(children[i]);
				}
				return;
			} else if (positive && at.getFunction() == t.mAnd) {
				// the axioms added below already imply the auxaxiom clauses.
				this.clausifier.setTermFlags(term, oldFlags | assertedFlag | auxFlag);
				// Assert all subformulas of the positive and.
				final Term[] params = at.getParameters();
				final AddAsAxiom[] children = new AddAsAxiom[params.length];
				for (int i = 0; i < params.length; i++) {
					final Term p = params[i];
					final Term split = this.clausifier.mTracker.resolveBinaryTautology(mAxiom, p, ProofConstants.TAUT_AND_NEG);
					children[i] = new AddAsAxiom(this.clausifier, split, mSource);
				}
				if (this.clausifier.satProofsEnabled()) {
					// and+ {term, ~p_1, .., ~p_k}, resolved with the children's p_i
					final Term[] startLits = new Term[params.length + 1];
					startLits[0] = term;
					for (int i = 0; i < params.length; i++) {
						startLits[i + 1] = t.term("not", params[i]);
					}
					this.clausifier.pushOperation(new SplitJoin(this, children, startLits, ProofConstants.TAUT_AND_POS));
				}
				for (int i = params.length - 1; i >= 0; i--) {
					this.clausifier.pushOperation(children[i]);
				}
				return;
			} else if (!positive && at.getFunction() == t.mImplies) {
				// the axioms added below already imply the auxaxiom clauses.
				this.clausifier.setTermFlags(term, oldFlags | assertedFlag | auxFlag);
				// A negated implication is an and of the left-hand formulas and the negated
				// right-hand formula. This asserts these formulas.
				final Term[] params = at.getParameters();
				final AddAsAxiom[] children = new AddAsAxiom[params.length];
				for (int i = 0; i < params.length; i++) {
					final Term p = i < params.length - 1 ? params[i] : t.term("not", params[i]);
					final Term split = this.clausifier.mTracker.resolveBinaryTautology(mAxiom, p, ProofConstants.TAUT_IMP_POS);
					children[i] = new AddAsAxiom(this.clausifier, split, mSource);
				}
				if (this.clausifier.satProofsEnabled()) {
					// =>- {~term, ~p_1, .., ~p_{n-1}, p_n}, resolved with the children's p_i / (not p_n)
					final Term[] startLits = new Term[params.length + 1];
					startLits[0] = t.term("not", term);
					for (int i = 0; i < params.length - 1; i++) {
						startLits[i + 1] = t.term("not", params[i]);
					}
					startLits[params.length] = params[params.length - 1];
					this.clausifier.pushOperation(new SplitJoin(this, children, startLits, ProofConstants.TAUT_IMP_NEG));
				}
				for (int i = params.length - 1; i >= 0; i--) {
					this.clausifier.pushOperation(children[i]);
				}
				return;
			} else if (at.getFunction().getName().equals("xor")
					&& at.getParameters()[0].getSort() == t.getBooleanSort()) {
				// the axioms added below already imply the auxaxiom clauses.
				this.clausifier.setTermFlags(term, oldFlags | assertedFlag | auxFlag);
				final Term p1 = at.getParameters()[0];
				final Term p2 = at.getParameters()[1];
				final Term pivot = positive ? t.term("not", term) : term;
				// the clauses mirror the aux-literal ones (Clausifier.createDefiningClausesForLiteral), with
				// rho = provedTerm(mAxiom) and its negation resolved away against mAxiom
				final Term rho = positive ? term : t.term("not", term);
				final Term notP1 = t.term("not", p1);
				// positive: (p1 \/ p2) /\ (~p1 \/ ~p2); negative: (p1 \/ ~p2) /\ (~p1 \/ p2)
				final Term q1 = positive ? p2 : t.term("not", p2);
				final Term q2 = positive ? t.term("not", p2) : p2;
				final Annotation rule1 = positive ? ProofConstants.TAUT_XOR_NEG_1 : ProofConstants.TAUT_XOR_POS_1;
				final Annotation rule2 = positive ? ProofConstants.TAUT_XOR_NEG_2 : ProofConstants.TAUT_XOR_POS_2;
				final Annotation dual1 = positive ? ProofConstants.TAUT_XOR_POS_1 : ProofConstants.TAUT_XOR_NEG_1;
				final Annotation dual2 = positive ? ProofConstants.TAUT_XOR_POS_2 : ProofConstants.TAUT_XOR_NEG_2;
				final Clausifier.ClauseSatProof cl1 = this.clausifier.buildClauseWithTautology(mAxiom, mSource,
						new Term[] { pivot, p1, q1 }, rule1, new Term[] { p1, rho },
						new Term[] { null, this.clausifier.satTaut(dual1, rho, p1, Clausifier.negate(q1)) });
				final Clausifier.ClauseSatProof cl2 = this.clausifier.buildClauseWithTautology(mAxiom, mSource,
						new Term[] { pivot, notP1, q2 }, rule2, new Term[] { notP1, rho },
						new Term[] { null, this.clausifier.satTaut(dual2, rho, notP1, Clausifier.negate(q2)) });
				mSatProof = this.clausifier.caseSplitRecord(cl1, cl2, p1, rho);
				return;
			} else if (at.getFunction().getName().equals("ite")) {
				// the axioms added below already imply the auxaxiom clauses.
				this.clausifier.setTermFlags(term, oldFlags | assertedFlag | auxFlag);
				assert at.getFunction().getReturnSort() == t.getBooleanSort();
				final Term cond = at.getParameters()[0];
				final Term thenForm = at.getParameters()[1];
				final Term elseForm = at.getParameters()[2];
				final Term pivot = positive ? t.term("not", term) : term;
				// mirrors the aux-literal clauses, see the xor case above
				final Term rho = positive ? term : t.term("not", term);
				final Term notCond = t.term("not", cond);
				final Term thenLit = positive ? thenForm : t.term("not", thenForm);
				final Term elseLit = positive ? elseForm : t.term("not", elseForm);
				final Annotation rule1 = positive ? ProofConstants.TAUT_ITE_NEG_1 : ProofConstants.TAUT_ITE_POS_1;
				final Annotation rule2 = positive ? ProofConstants.TAUT_ITE_NEG_2 : ProofConstants.TAUT_ITE_POS_2;
				final Annotation dual1 = positive ? ProofConstants.TAUT_ITE_POS_1 : ProofConstants.TAUT_ITE_NEG_1;
				final Annotation dual2 = positive ? ProofConstants.TAUT_ITE_POS_2 : ProofConstants.TAUT_ITE_NEG_2;
				final Clausifier.ClauseSatProof cl1 = this.clausifier.buildClauseWithTautology(mAxiom, mSource,
						new Term[] { pivot, notCond, thenLit }, rule1, new Term[] { notCond, rho },
						new Term[] { null, this.clausifier.satTaut(dual1, rho, notCond, Clausifier.negate(thenLit)) });
				final Clausifier.ClauseSatProof cl2 = this.clausifier.buildClauseWithTautology(mAxiom, mSource,
						new Term[] { pivot, cond, elseLit }, rule2, new Term[] { cond, rho },
						new Term[] { null, this.clausifier.satTaut(dual2, rho, cond, Clausifier.negate(elseLit)) });
				mSatProof = this.clausifier.caseSplitRecord(cl1, cl2, cond, rho);
				return;
			}
		} else if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula qf = (QuantifiedFormula) term;
			final Pair<Term, Annotation> convertQuantInfo = this.clausifier.convertQuantifiedSubformula(positive, qf);
			final Annotation rule = convertQuantInfo.getSecond();
			final Term substituted = convertQuantInfo.getFirst();
			final Term skolemized = this.clausifier.mTracker.resolveBinaryTautology(mAxiom, substituted, rule);
			final Term rewrite = this.clausifier.mCompiler.transform(this.clausifier.mTracker.getProvedTerm(skolemized));
			final Term newAxiom = this.clausifier.mTracker.modusPonens(skolemized, rewrite);
			final AddAsAxiom child = new AddAsAxiom(this.clausifier, newAxiom, mSource);
			if (this.clausifier.satProofsEnabled()) {
				// the sat dual {lit, ~substituted} (forallIntro/existsElim at the choose terms, resp. existsIntro/
				// forallElim at the skolem terms), resolved with the reversed compile rewrite {~newAxiom, substituted}
				final Term lit = positive ? term : t.term("not", term);
				final Term canonic = this.clausifier.mTracker.getProvedTerm(rewrite);
				Term start = this.clausifier.mTracker.getClauseProof(this.clausifier.mTracker.tautology(
						t.term("or", lit, Clausifier.negate(substituted)), Clausifier.dualQuantifierRule(rule)));
				final Term reverse = this.clausifier.mTracker.rewriteToClauseReverse(substituted, rewrite);
				if (reverse != null) {
					start = ((ProofTracker) this.clausifier.mTracker).resolve(substituted,
							this.clausifier.mTracker.getClauseProof(reverse), start);
				}
				final Term[] startLits = new Term[] { lit, Clausifier.negate(canonic) };
				this.clausifier.pushOperation(new SplitJoin(this, new AddAsAxiom[] { child }, startLits, start));
			}
			this.clausifier.pushOperation(child);
			return;
		}
		setLeafSatProof(this.clausifier.buildClause(mAxiom, mSource));
	}

	/**
	 * Runs after all children of a propositional split (and+/or-/=>-) have finished, and composes their sat-proof
	 * records into one for the parent: the dual tautology as start proof, resolved with each child's record on the
	 * child's formula. Pushed under the children so it runs after them (the todo stack is LIFO).
	 */
	private static final class SplitJoin implements Operation {
		private final AddAsAxiom mParent;
		private final AddAsAxiom[] mChildren;
		/** The literals of the dual tautology: the parent's formula and the negations of the children's. */
		private final Term[] mStartLits;
		private final Annotation mRule;
		/** The start proof, if it is not just the tautology {@code mStartLits} (then {@code mRule} is null). */
		private final Term mStart;

		SplitJoin(final AddAsAxiom parent, final AddAsAxiom[] children, final Term[] startLits,
				final Annotation rule) {
			mParent = parent;
			mChildren = children;
			mStartLits = startLits;
			mRule = rule;
			mStart = null;
		}

		SplitJoin(final AddAsAxiom parent, final AddAsAxiom[] children, final Term[] startLits, final Term start) {
			mParent = parent;
			mChildren = children;
			mStartLits = startLits;
			mRule = null;
			mStart = start;
		}

		@Override
		public void perform() {
			final Clausifier clausifier = mParent.clausifier;
			final Clausifier.SatRecord[] hyps = new Clausifier.SatRecord[mChildren.length];
			final Term[] pivots = new Term[mChildren.length];
			for (int i = 0; i < mChildren.length; i++) {
				if (mChildren[i].mSatProof == null) {
					// A child's own derivation isn't available (e.g. it went through an
					// unimplemented branch) -- the whole join falls back too.
					mParent.mSatProof = null;
					return;
				}
				hyps[i] = mChildren[i].mSatProof;
				pivots[i] = clausifier.mTracker.getProvedTerm(mChildren[i].mAxiom);
			}
			final Theory t = mParent.mAxiom.getTheory();
			final Term start = mStart != null ? mStart
					: clausifier.mTracker.getClauseProof(clausifier.mTracker.tautology(t.term("or", mStartLits), mRule));
			mParent.mSatProof = clausifier.formulaSatProof(start, mStartLits, hyps, pivots,
					clausifier.mTracker.getProvedTerm(mParent.mAxiom));
		}
	}
}
