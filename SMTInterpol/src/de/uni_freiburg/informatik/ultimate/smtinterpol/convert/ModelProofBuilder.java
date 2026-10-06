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

import java.util.Arrays;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.ModelProver;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.ProofLiteral;

/**
 * Assembles a model (sat) proof from the sat-proof records the clausifier recorded
 * ({@link Clausifier#mAssertionSatProofs}/{@link Clausifier#mLiteralSatProofs}) and the DPLL engine's final
 * assignment, falling back to evaluating a literal or assertion directly with {@link ModelProver} wherever a
 * record is missing or incomplete. All record proofs are clause proofs in the "stripped" convention (a literal
 * {@code (not x)} is the negative literal of {@code x}); the conversions to and from the "opaque" convention of
 * {@link ModelProver} and of the final {@code (and assertions)} happen only in {@link #proveLiteral} and
 * {@link #buildProof}. See SMTInterpol/doc/model-proof-plan.md, "The aux-clause contract" and "Assembling the
 * proof at sat time".
 *
 * @author Jochen Hoenicke
 */
public class ModelProofBuilder {
	private final Clausifier mClausifier;
	private final ModelProver mModelProver;
	private final ProofTracker mTracker;
	private final Theory mTheory;
	/** Memo per record; {@link #FAILED} for a record that could not be proved structurally. */
	private final IdentityHashMap<Clausifier.SatRecord, ProvedClause> mMemo = new IdentityHashMap<>();
	private static final ProvedClause FAILED = new ProvedClause(null, null);

	/** A clause proof together with the clause it proves (canonical literals). */
	private static final class ProvedClause {
		final Term mProof;
		final Set<ProofLiteral> mClause;

		ProvedClause(final Term proof, final Set<ProofLiteral> clause) {
			mProof = proof;
			mClause = clause;
		}
	}

	public ModelProofBuilder(final Clausifier clausifier, final ModelProver modelProver) {
		mClausifier = clausifier;
		mModelProver = modelProver;
		mTracker = (ProofTracker) clausifier.mTracker;
		mTheory = clausifier.getTheory();
		modelProver.setBooleanTermProver(this::proveBooleanTerm);
	}

	/**
	 * The {@link ModelProver.BooleanTermProver} hook: prove a Boolean subterm the model prover would otherwise
	 * evaluate (an argument of an uninterpreted function, a term-ite condition, ...) from the sat-proof record of
	 * its clausifier literal. The model has no values for Boolean terms; for quantified subterms this is the only
	 * way to prove them.
	 *
	 * @return the annotated proof (see {@link ModelProver#annotateValue}), or null if there is no complete record.
	 */
	private Term proveBooleanTerm(final Term term) {
		final ILiteral lit = mClausifier.getILiteral(term);
		if (lit == null) {
			return null;
		}
		final boolean value;
		final ILiteral trueLit;
		if (isTrue(lit)) {
			value = true;
			trueLit = lit;
		} else if (isTrue(lit.negate())) {
			value = false;
			trueLit = lit.negate();
		} else {
			return null;
		}
		final Clausifier.FormulaSatProof record = mClausifier.mLiteralSatProofs.get(trueLit);
		if (record == null) {
			return null;
		}
		// only the record, never the model prover fallback: that would evaluate term again
		final Term proof = proveRecord(record, new ProofLiteral(term, value));
		return proof == null ? null : ModelProver.annotateValue(proof, value);
	}

	private static Set<ProofLiteral> clauseOf(final ProofLiteral... lits) {
		return new HashSet<>(Arrays.asList(lits));
	}

	/**
	 * Resolve two clause proofs on {@code atom}; {@code proofPos} is the one containing {@code atom} positively.
	 */
	private Term res(final Term atom, final Term proofPos, final Term proofNeg) {
		return mTracker.getProofRules().resolutionRule(atom, proofPos, proofNeg);
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

	/** Returns a proof of the unit clause {@code {l}} (stripped convention). */
	private Term proveLiteral(final ILiteral l) {
		final Term formula = l.getSMTFormula(mTheory);
		final Clausifier.FormulaSatProof record = mClausifier.mLiteralSatProofs.get(l);
		if (record != null) {
			final Term proof = proveRecord(record, Clausifier.toProofLiteral(formula));
			if (proof != null) {
				return proof;
			}
		}
		// ModelProver proves {+formula} with formula used opaquely
		return mTracker.stripNot(formula, true, mModelProver.proveAtom(formula));
	}

	/**
	 * Prove a record and check that it proves exactly {@code {conclusion}}.
	 *
	 * @return the proof, or null if the record is incomplete.
	 */
	private Term proveRecord(final Clausifier.SatRecord record, final ProofLiteral conclusion) {
		final ProvedClause pc = prove(record);
		if (pc == FAILED) {
			return null;
		}
		if (pc.mClause.size() != 1 || !pc.mClause.contains(conclusion)) {
			// e.g. the open createExcludedMiddleSatProof case, see the model-proof plan
			return null;
		}
		return pc.mProof;
	}

	private ProvedClause prove(final Clausifier.SatRecord record) {
		ProvedClause result = mMemo.get(record);
		if (result == null) {
			// guard against cycles through the BooleanTermProver hook
			mMemo.put(record, FAILED);
			if (record instanceof Clausifier.ClauseSatProof) {
				result = proveClause((Clausifier.ClauseSatProof) record);
			} else {
				result = proveFormula((Clausifier.FormulaSatProof) record);
			}
			mMemo.put(record, result);
		}
		return result;
	}

	/** Proves the target of {@code c} (or a subclause of it) from the literal the model sets true. */
	private ProvedClause proveClause(final Clausifier.ClauseSatProof c) {
		if (c.mReadyMadeProof != null) {
			return new ProvedClause(c.mReadyMadeProof, clauseOf(c.mTarget));
		}
		if (c.mLiterals == null) {
			// incomplete record (poisoned or trivially true clause)
			return FAILED;
		}
		for (final Map.Entry<ILiteral, Clausifier.SatEntry> e : c.mLiterals.entrySet()) {
			final ILiteral l = e.getKey();
			if (!isTrue(l)) {
				continue;
			}
			final Clausifier.SatEntry entry = e.getValue();
			Term proof = proveLiteral(l);
			if (entry.mProof != null) {
				// proof proves {l}, entry.mProof proves {~l, mDisjunct} resp. {~l} ∪ target
				final ProofLiteral lit = Clausifier.toProofLiteral(l.getSMTFormula(mTheory));
				proof = lit.getPolarity() ? res(lit.getAtom(), proof, entry.mProof)
						: res(lit.getAtom(), entry.mProof, proof);
			}
			final Set<ProofLiteral> clause =
					entry.mDisjunct == null ? clauseOf(c.mTarget) : clauseOf(entry.mDisjunct);
			return new ProvedClause(proof, clause);
		}
		// No literal of this clause is set to true. Shouldn't happen (see the "invariant the assembler relies on"
		// in the model-proof plan) but degrade gracefully rather than crash.
		return FAILED;
	}

	/**
	 * Proves a record's conclusion: start with the start proof (or the first hyp), then resolve each further hyp
	 * on its pivot atom. The side containing the atom positively is the positive antecedent; a step is skipped if
	 * the atom does not occur with opposite polarities on the two sides (the default case of a match can prove a
	 * strict subclause of its target).
	 */
	private ProvedClause proveFormula(final Clausifier.FormulaSatProof f) {
		Term proof = f.mStart;
		Set<ProofLiteral> clause = f.mStart == null ? null : clauseOf(f.mStartClause);
		for (int i = 0; i < f.mHyps.length; i++) {
			final ProvedClause hyp = prove(f.mHyps[i]);
			if (hyp == FAILED) {
				return FAILED;
			}
			if (proof == null) {
				proof = hyp.mProof;
				clause = new HashSet<>(hyp.mClause);
				continue;
			}
			final Term atom = f.mPivots[i];
			final ProofLiteral pos = new ProofLiteral(atom, true);
			final ProofLiteral neg = pos.negate();
			final ProofLiteral inHyp;
			if (hyp.mClause.contains(pos) && clause.contains(neg)) {
				proof = res(atom, hyp.mProof, proof);
				inHyp = pos;
			} else if (hyp.mClause.contains(neg) && clause.contains(pos)) {
				proof = res(atom, proof, hyp.mProof);
				inHyp = neg;
			} else {
				continue;
			}
			clause.remove(inHyp.negate());
			for (final ProofLiteral l : hyp.mClause) {
				if (!l.equals(inHyp)) {
					clause.add(l);
				}
			}
		}
		return new ProvedClause(proof, clause);
	}

	/**
	 * Assemble the model proof for the given assertions (in order): a proof of the unit clause
	 * {@code {(and assertions)}}, without the refineFun/defineFun prefix -- the caller adds that, see
	 * {@link ModelProver#wrapRefineFun}.
	 */
	public Term buildProof(final List<Term> assertions) {
		if (assertions.size() == 0) {
			return mTracker.getProofRules().trueIntro();
		}

		final Term[] assertionArray = assertions.toArray(new Term[assertions.size()]);
		Term proof = null;
		if (assertionArray.length > 1) {
			proof = mTracker.getProofRules().andIntro(mTheory.term(SMTLIBConstants.AND, assertionArray));
		}
		for (int i = 0; i < assertionArray.length; i++) {
			final Term a = assertionArray[i];
			final Clausifier.SatRecord record = mClausifier.mAssertionSatProofs.get(a);
			Term aProof = record == null ? null : proveRecord(record, Clausifier.toProofLiteral(a));
			// andIntro (and checkModelProof) use the assertion opaquely
			aProof = aProof != null ? mTracker.wrapNot(a, true, aProof) : mModelProver.proveAtom(a);
			proof = proof == null ? aProof : mTracker.resolveAtom(a, aProof, proof);
		}
		return proof;
	}
}
