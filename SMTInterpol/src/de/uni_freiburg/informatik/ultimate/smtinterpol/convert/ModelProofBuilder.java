/*
 * Copyright (C) 2026 University of Freiburg
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

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.ModelProver;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofTracker;

/**
 * Assembles a model (sat) proof from the sat-proof artifacts the clausifier
 * recorded ({@link Clausifier#mAssertionSatProofs}/{@link Clausifier#mLiteralSatProofs})
 * and the DPLL engine's final assignment, falling back to evaluating a
 * (sub)formula directly with {@link ModelProver} wherever the structural
 * tracking is incomplete (not yet implemented, or genuinely unavailable, e.g.
 * a trivially true clause). See SMTInterpol/doc/model-proof-plan.md,
 * "Assembling the proof at sat time".
 *
 * @author Jochen Hoenicke
 */
public class ModelProofBuilder {
	private final Clausifier mClausifier;
	private final ModelProver mModelProver;
	private final ProofTracker mTracker;
	private final Theory mTheory;

	public ModelProofBuilder(final Clausifier clausifier, final ModelProver modelProver) {
		mClausifier = clausifier;
		mModelProver = modelProver;
		mTracker = (ProofTracker) clausifier.mTracker;
		mTheory = clausifier.getTheory();
	}

	private static Term stripNotTerm(Term t) {
		while (Clausifier.isNotTerm(t)) {
			t = Clausifier.toPositive(t);
		}
		return t;
	}

	private boolean isTrue(final ILiteral l) {
		if (l instanceof Literal) {
			final Literal lit = (Literal) l;
			final DPLLAtom atom = lit.getAtom();
			return atom.getDecideStatus() == lit;
		}
		// QuantLiteral and others: quantified clauses are phase 4, not reached here.
		return false;
	}

	/** Returns a proof of the unit clause containing {@code l} itself, signed. */
	private Term proveLiteral(final ILiteral l) {
		final Clausifier.FormulaSatProof record = mClausifier.mLiteralSatProofs.get(l);
		if (record != null) {
			return proveFormula(record);
		}
		return mModelProver.proveAtom(l.getSMTFormula(mTheory));
	}

	/** Returns a proof of {@code {c.mFormula+}}, memoized in {@code c.mAssembled}. */
	private Term proveClause(final Clausifier.ClauseSatProof c) {
		if (c.mAssembled != null) {
			return c.mAssembled;
		}
		Term result = null;
		if (c.mReadyMadeProof != null) {
			result = c.mReadyMadeProof;
		} else if (c.mLiterals != null) {
			result = proveFromLiterals(c);
		}
		if (result == null) {
			// No (usable) structural derivation for this clause -- evaluate it directly.
			result = mModelProver.proveAtom(c.mFormula);
		}
		c.mAssembled = result;
		return result;
	}

	private Term proveFromLiterals(final Clausifier.ClauseSatProof c) {
		for (final Map.Entry<ILiteral, Clausifier.SatEntry> e : c.mLiterals.entrySet()) {
			final ILiteral l = e.getKey();
			if (!isTrue(l)) {
				continue;
			}
			final Clausifier.SatEntry entry = e.getValue();
			if (entry.mDisjunct != c.mFormula) {
				// TODO: bridge disjunct -> mFormula via orIntro, for multi-literal "or"
				// clause formulas (see the model-proof plan); not yet implemented.
				return null;
			}
			final Term litFormula = l.getSMTFormula(mTheory);
			final Term litProof = proveLiteral(l);
			if (entry.mProof == null) {
				return litProof;
			}
			// litProof concludes litFormula opaquely (see ModelProver), while entry.mProof
			// -- built via BuildClause's reversed-rewrite composition -- uses the "always
			// stripped" clause-literal convention; strip litProof down to match before
			// folding the two together. Stripping keeps litProof's own sign for the core
			// atom (positive iff litFormula is, i.e. iff l is a positive literal), while
			// entry.mProof -- built from the reverse of the *same* rewrite -- always has
			// the opposite sign for it; so which one plays "proofPos" flips with l's polarity.
			final Term core = stripNotTerm(litFormula);
			final Term strippedLitProof = mTracker.stripNot(litFormula, true, litProof);
			return Clausifier.isNotTerm(litFormula) ? mTracker.resolveAtom(core, entry.mProof, strippedLitProof)
					: mTracker.resolveAtom(core, strippedLitProof, entry.mProof);
		}
		// No literal of this clause is set to true. Shouldn't happen (see the
		// "invariant the assembler relies on" in the model-proof plan) but degrade
		// gracefully rather than crash.
		return null;
	}

	/** Returns a proof of {@code {f.mHyps[i].mFormula+}}'s combined conclusion, i.e. what {@code f} proves. */
	private Term proveFormula(final Clausifier.FormulaSatProof f) {
		if (f.mProof == null) {
			assert f.mHyps.length == 1;
			return proveClause(f.mHyps[0]);
		}
		Term proof = f.mProof;
		for (final Clausifier.ClauseSatProof hyp : f.mHyps) {
			proof = mTracker.resolveAtom(hyp.mFormula, proveClause(hyp), proof);
		}
		return proof;
	}

	/**
	 * Assemble the model proof for the given assertions (in order): a proof of
	 * the unit clause {@code {(and assertions)}}, without the refineFun/defineFun
	 * prefix -- the caller adds that, see {@link ModelProver#wrapRefineFun}.
	 */
	public Term buildProof(final List<Term> assertions) {
		final Term[] proofs = new Term[assertions.size()];
		for (int i = 0; i < assertions.size(); i++) {
			final Term a = assertions.get(i);
			final Clausifier.FormulaSatProof record = mClausifier.mAssertionSatProofs.get(a);
			proofs[i] = record != null ? proveFormula(record) : mModelProver.proveAtom(a);
		}
		if (proofs.length == 1) {
			return proofs[0];
		}
		final Term andTerm = mTheory.term(SMTLIBConstants.AND, assertions.toArray(new Term[assertions.size()]));
		// andIntro(andTerm) = {andTerm, ~a_1, .., ~a_n}, using the assertions themselves as
		// opaque literals (unlike tautology(), which would strip "not"s from them).
		Term proof = mTracker.andIntro(andTerm);
		for (int i = 0; i < proofs.length; i++) {
			proof = mTracker.resolveAtom(assertions.get(i), proofs[i], proof);
		}
		return proof;
	}
}
