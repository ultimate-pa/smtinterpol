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

import java.util.ArrayList;
import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
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
	 * when this node's derivation isn't (yet) tracked, e.g. xor/ite/quantified
	 * formulas (see the model-proof plan, phases 2/4) or a formula that turned out
	 * to already be asserted; the caller then falls back to evaluating the formula
	 * directly instead of using this record.
	 */
	Clausifier.FormulaSatProof mSatProof;

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

	/** Record a leaf clause's sat-proof record as this node's own (identity: mAxiom's formula is its own clause formula). */
	private void setLeafSatProof(final Clausifier.ClauseSatProof csp) {
		if (csp != null) {
			mSatProof = new Clausifier.FormulaSatProof(null, new Clausifier.ClauseSatProof[] { csp });
		}
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
					// orElim(term) = {~term, p_1, .., p_k}, using term's own params as opaque
					// literals (unlike tautology(), which strips "not"s); rho-bridged to
					// {rho, p_1, .., p_k}; each p_i is then child-bridged to ~(not p_i), since
					// child_i's own formula is (not p_i).
					final ProofTracker tracker = (ProofTracker) this.clausifier.mTracker;
					Term dualTaut = tracker.orElim(term);
					dualTaut = rhoBridge(tracker, dualTaut, term);
					final boolean[] childBridge = new boolean[params.length];
					Arrays.fill(childBridge, true);
					this.clausifier.pushOperation(new SplitJoin(this, children, dualTaut, childBridge));
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
					// andIntro(term) = {rho, ~p_1, .., ~p_k}, using term's own params as opaque
					// literals; rho == term (positive), no rho-bridge needed, and child_i's own
					// formula is p_i itself (opaque), so no child-bridge is needed either.
					final Term dualTaut = ((ProofTracker) this.clausifier.mTracker).andIntro(term);
					this.clausifier.pushOperation(new SplitJoin(this, children, dualTaut, new boolean[params.length]));
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
					// impElim(term) = {~term, ~p_1, .., ~p_{n-1}, p_n}, using term's own params
					// as opaque literals; rho-bridged; only the last child (whose own formula is
					// (not p_n)) needs a child-bridge, since the others' formula is p_i itself.
					final ProofTracker tracker = (ProofTracker) this.clausifier.mTracker;
					Term dualTaut = tracker.impElim(term);
					dualTaut = rhoBridge(tracker, dualTaut, term);
					final boolean[] childBridge = new boolean[params.length];
					childBridge[params.length - 1] = true;
					this.clausifier.pushOperation(new SplitJoin(this, children, dualTaut, childBridge));
				}
				for (int i = params.length - 1; i >= 0; i--) {
					this.clausifier.pushOperation(children[i]);
				}
				return;
			} else if (at.getFunction().getName().equals("xor")
					&& at.getParameters()[0].getSort() == t.getBooleanSort()) {
				// the axioms added below already imply the auxaxiom clauses.
				this.clausifier.setTermFlags(term, oldFlags | assertedFlag | auxFlag);
				// TODO: track the sat-side dual (phase 2 of the model-proof plan, mirroring
				// the aux-literal ite/xor derivation). mSatProof stays null; the caller falls
				// back to evaluating the assertion directly.
				final Term p1 = at.getParameters()[0];
				final Term p2 = at.getParameters()[1];
				if (positive) {
					// (xor p1 p2) --> (p1 \/ p2) /\ (~p1 \/ ~p2)
					final Term pivot = t.term("not", term);
					this.clausifier.buildClauseWithTautology(mAxiom, mSource, new Term[] { pivot, p1, p2 },
							ProofConstants.TAUT_XOR_NEG_1);
					this.clausifier.buildClauseWithTautology(mAxiom, mSource,
							new Term[] { pivot, t.term("not", p1), t.term("not", p2) },
							ProofConstants.TAUT_XOR_NEG_2);
				} else {
					// (not (xor p1 p2)) --> (p1 \/ ~p2) /\ (~p1 \/ p2)
					final Term pivot = term;
					this.clausifier.buildClauseWithTautology(mAxiom, mSource, new Term[] { pivot, p1, t.term("not", p2) },
							ProofConstants.TAUT_XOR_POS_1);
					this.clausifier.buildClauseWithTautology(mAxiom, mSource, new Term[] { pivot, t.term("not", p1), p2 },
							ProofConstants.TAUT_XOR_POS_2);
				}
				return;
			} else if (at.getFunction().getName().equals("ite")) {
				// the axioms added below already imply the auxaxiom clauses.
				this.clausifier.setTermFlags(term, oldFlags | assertedFlag | auxFlag);
				// TODO: track the sat-side dual (phase 2 of the model-proof plan). mSatProof
				// stays null; the caller falls back to evaluating the assertion directly.
				assert at.getFunction().getReturnSort() == t.getBooleanSort();
				final Term cond = at.getParameters()[0];
				final Term thenForm = at.getParameters()[1];
				final Term elseForm = at.getParameters()[2];
				if (positive) {
					final Term pivot = t.term("not", term);
					this.clausifier.buildClauseWithTautology(mAxiom, mSource, new Term[] { pivot, t.term("not", cond), thenForm },
							ProofConstants.TAUT_ITE_NEG_1);
					this.clausifier.buildClauseWithTautology(mAxiom, mSource, new Term[] { pivot, cond, elseForm },
							ProofConstants.TAUT_ITE_NEG_2);
				} else {
					final Term pivot = term;
					this.clausifier.buildClauseWithTautology(mAxiom, mSource,
							new Term[] { pivot, t.term("not", cond), t.term("not", thenForm) },
							ProofConstants.TAUT_ITE_POS_1);
					this.clausifier.buildClauseWithTautology(mAxiom, mSource, new Term[] { pivot, cond, t.term("not", elseForm) },
							ProofConstants.TAUT_ITE_POS_2);
				}
				return;
			}
		} else if (term instanceof QuantifiedFormula) {
			// TODO: track the sat-side dual (phase 4 of the model-proof plan). mSatProof
			// stays null; the caller falls back to evaluating the assertion directly.
			final QuantifiedFormula qf = (QuantifiedFormula) term;
			final Pair<Term, Annotation> convertQuantInfo = this.clausifier.convertQuantifiedSubformula(positive, qf);
			final Annotation rule = convertQuantInfo.getSecond();
			final Term skolemized = this.clausifier.mTracker.resolveBinaryTautology(mAxiom, convertQuantInfo.getFirst(), rule);
			final Term rewrite = this.clausifier.mCompiler.transform(this.clausifier.mTracker.getProvedTerm(skolemized));
			final Term newAxiom = this.clausifier.mTracker.modusPonens(skolemized, rewrite);
			this.clausifier.pushOperation(new AddAsAxiom(this.clausifier, newAxiom, mSource));
			return;
		}
		setLeafSatProof(this.clausifier.buildClause(mAxiom, mSource));
	}

	/**
	 * Turn {@code {~term, ...}} (what {@code orElim(term)}/{@code impElim(term)}
	 * naturally gives for their own negated first literal) into
	 * {@code {+(not term), ...}}, matching a negatively-asserted node's own raw,
	 * opaque {@code provedTerm(mAxiom)}.
	 */
	private static Term rhoBridge(final ProofTracker tracker, final Term proof, final Term term) {
		final Term notTerm = term.getTheory().term(SMTLIBConstants.NOT, term);
		return tracker.wrapNot(notTerm, true, proof);
	}

	/**
	 * Runs after all children of a propositional split (and+/or-/=>-) have
	 * finished, and composes their sat-proof records into one for the parent, via
	 * the dual tautology. See "Input clauses and assertions" in the model-proof
	 * plan; pushed under the children so it runs after them (the todo stack is
	 * LIFO).
	 */
	private static final class SplitJoin implements Operation {
		private final AddAsAxiom mParent;
		private final AddAsAxiom[] mChildren;
		/**
		 * Proof of {@code {provedTerm(mParent.mAxiom), d_1, .., d_n}}, where
		 * {@code d_i} is child i's own formula {@code provedTerm(children[i].mAxiom)}
		 * if {@code mChildBridge[i]} is false, else the underlying atom of that
		 * (then "not"-headed) formula, opaquely and positively (see
		 * {@link ProofTracker#wrapNot}).
		 */
		private final Term mDualTaut;
		/**
		 * For each child, whether {@link ProofTracker#wrapNot} is needed to turn
		 * {@code mDualTaut}'s slot into {@code ~provedTerm(children[i].mAxiom)}
		 * before folding the child in -- true exactly when that formula is itself
		 * "not"-headed but the dual tautology's own construction (orElim/impElim,
		 * tied to the parent's un-negated params) offers its underlying atom instead.
		 */
		private final boolean[] mChildBridge;

		SplitJoin(final AddAsAxiom parent, final AddAsAxiom[] children, final Term dualTaut, final boolean[] childBridge) {
			mParent = parent;
			mChildren = children;
			mDualTaut = dualTaut;
			mChildBridge = childBridge;
		}

		@Override
		public void perform() {
			for (final AddAsAxiom child : mChildren) {
				if (child.mSatProof == null) {
					// A child's own derivation isn't available (e.g. it went through an
					// unimplemented branch) -- the whole join falls back too.
					mParent.mSatProof = null;
					return;
				}
			}
			final ProofTracker tracker = (ProofTracker) mParent.clausifier.mTracker;
			Term proof = mDualTaut;
			final ArrayList<Clausifier.ClauseSatProof> hyps = new ArrayList<>();
			for (int i = 0; i < mChildren.length; i++) {
				final Term psi = mParent.clausifier.mTracker.getProvedTerm(mChildren[i].mAxiom);
				if (mChildBridge[i]) {
					// The dual tautology naturally has +p at this slot (p = psi's own, opaque
					// argument, since orElim/impElim don't peel INTO their params any further
					// than the parent's own structure); turn it into ~psi = ~(not p).
					final Term p = ((ApplicationTerm) psi).getParameters()[0];
					proof = tracker.resolveAtom(p, proof, tracker.notElim(psi));
				}
				final Clausifier.FormulaSatProof childProof = mChildren[i].mSatProof;
				if (childProof.mProof != null) {
					proof = tracker.resolveAtom(psi, childProof.mProof, proof);
				}
				for (final Clausifier.ClauseSatProof hyp : childProof.mHyps) {
					hyps.add(hyp);
				}
			}
			mParent.mSatProof =
					new Clausifier.FormulaSatProof(proof, hyps.toArray(new Clausifier.ClauseSatProof[hyps.size()]));
		}
	}
}
