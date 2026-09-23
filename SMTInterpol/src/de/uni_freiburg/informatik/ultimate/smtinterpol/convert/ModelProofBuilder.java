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

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
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
		final Clausifier.NWayAuxProof nway = mClausifier.mNWayAuxProofs.get(l);
		if (nway != null) {
			final Term proof = proveNWay(nway);
			if (proof != null) {
				return proof;
			}
		}
		return mModelProver.proveAtom(l.getSMTFormula(mTheory));
	}

	/**
	 * Returns a proof of {@code {+rec.mTerm}} (or-positive) or {@code {+(not
	 * rec.mTerm)}} (and-negative) or {@code {+rec.mTerm}} (=>-positive): picks
	 * whichever of {@code rec.mTerm}'s params justifies the literal in the
	 * model -- not decidable at clause-construction time, see
	 * {@link Clausifier.NWayAuxProof} -- then builds the checked-axiom-based
	 * proof for that one choice on the fly. Returns {@code null} if (contrary
	 * to the invariant the assembler relies on) no choice fits.
	 */
	private Term proveNWay(final Clausifier.NWayAuxProof rec) {
		final Term[] params = ((ApplicationTerm) rec.mTerm).getParameters();
		switch (rec.mKind) {
		case OR_POSITIVE:
			// term true iff some p_i is true; orIntro(i,term) = {+term, ~p_i}.
			for (int i = 0; i < params.length; i++) {
				final Term probe = params[i];
				if (mModelProver.evaluateBoolean(probe)) {
					return mTracker.resolveAtom(probe, mModelProver.proveAtom(probe), mTracker.orIntro(i, rec.mTerm));
				}
			}
			break;
		case AND_NEGATIVE: {
			// (not term) true iff some p_i is false; andElim(i,term) = {~term, +p_i},
			// wrapped so ~term becomes +(not term).
			final Term notTerm = mTheory.term(SMTLIBConstants.NOT, rec.mTerm);
			for (int i = 0; i < params.length; i++) {
				final Term probe = params[i];
				if (!mModelProver.evaluateBoolean(probe)) {
					final Term wrapped = mTracker.wrapNot(notTerm, true, mTracker.andElim(i, rec.mTerm));
					return mTracker.resolveAtom(probe, wrapped, mModelProver.proveAtom(probe));
				}
			}
			break;
		}
		case IMPLIES_POSITIVE: {
			final int last = params.length - 1;
			for (int i = 0; i < last; i++) {
				final Term probe = params[i];
				if (!mModelProver.evaluateBoolean(probe)) {
					// premise i false -- impIntro(i,term) = {+term, +p_i}.
					return mTracker.resolveAtom(probe, mTracker.impIntro(i, rec.mTerm), mModelProver.proveAtom(probe));
				}
			}
			final Term concl = params[last];
			if (mModelProver.evaluateBoolean(concl)) {
				// conclusion true -- impIntro(last,term) = {+term, ~p_last}.
				return mTracker.resolveAtom(concl, mModelProver.proveAtom(concl), mTracker.impIntro(last, rec.mTerm));
			}
			break;
		}
		}
		return null;
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
			final Term litFormula = l.getSMTFormula(mTheory);
			final Term litProof = proveLiteral(l);
			Term proof;
			if (entry.mProof == null) {
				proof = litProof;
			} else {
				// litProof concludes litFormula opaquely (see ModelProver), while entry.mProof
				// -- built via BuildClause's reversed-rewrite composition -- uses the "always
				// stripped" clause-literal convention; strip litProof down to match before
				// folding the two together. Stripping keeps litProof's own sign for the core
				// atom (positive iff litFormula is, i.e. iff l is a positive literal), while
				// entry.mProof -- built from the reverse of the *same* rewrite -- always has
				// the opposite sign for it; so which one plays "proofPos" flips with l's polarity.
				final Term core = stripNotTerm(litFormula);
				final Term strippedLitProof = mTracker.stripNot(litFormula, true, litProof);
				proof = Clausifier.isNotTerm(litFormula) ? mTracker.resolveAtom(core, entry.mProof, strippedLitProof)
						: mTracker.resolveAtom(core, strippedLitProof, entry.mProof);
				// The fold above lands on entry.mDisjunct's own "always stripped" core, at
				// whichever sign that leaves it (core == stripNotTerm(entry.mDisjunct) by
				// construction); wrap it back up to the opaque {+entry.mDisjunct} the rest of
				// this method (and its callers) expect. A no-op when mDisjunct has no leading
				// "not" of its own.
				proof = mTracker.wrapNot(entry.mDisjunct, true, proof);
			}
			// proof concludes {+entry.mDisjunct}; when the clause formula is a
			// multi-literal "or" and entry.mDisjunct is just one of its disjuncts (aux
			// clauses, e.g. Tseitin definitions), bridge it up to {+c.mFormula} via orIntro.
			if (entry.mDisjunct != c.mFormula) {
				final int pos = disjunctIndex(c.mFormula, entry.mDisjunct);
				if (pos < 0) {
					// Shouldn't happen (entry.mDisjunct is always one of c.mFormula's own
					// disjuncts by construction) but degrade gracefully rather than crash.
					return null;
				}
				proof = mTracker.resolveAtom(entry.mDisjunct, proof, mTracker.orIntro(pos, c.mFormula));
			}
			return proof;
		}
		// No literal of this clause is set to true. Shouldn't happen (see the
		// "invariant the assembler relies on" in the model-proof plan) but degrade
		// gracefully rather than crash.
		return null;
	}

	/** Index of {@code disjunct} among {@code orTerm}'s params, or -1 if not found/not an "or". */
	private static int disjunctIndex(final Term orTerm, final Term disjunct) {
		if (!(orTerm instanceof ApplicationTerm)) {
			return -1;
		}
		final Term[] params = ((ApplicationTerm) orTerm).getParameters();
		for (int i = 0; i < params.length; i++) {
			if (params[i] == disjunct) {
				return i;
			}
		}
		return -1;
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
