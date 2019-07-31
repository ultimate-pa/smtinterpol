/*
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.ematching;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantBoundConstraint;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifierTheory;

/**
 * The E-Matching engine. Patterns are compiled to code that will be executed step by step in order to find new
 * interesting substitutions for the variables in the patterns. Some pieces of code may install triggers in the
 * congruence closure such that the remaining code is only executed when the trigger is activated.
 * 
 * @author Tanja Schindler
 */
public class EMatching {

	private final QuantifierTheory mQuantTheory;
	private final Deque<Pair<ICode, CCTerm[]>> mTodoStack;
	private final Map<Integer, EMUndoInformation> mUndoInformation;
	/**
	 * For each quantified literal, the interesting substitutions and the corresponding CCTerms for the occurring
	 * EUTerms.
	 */
	private final Map<QuantLiteral, List<Pair<Map<Term, CCTerm>, Map<Term, CCTerm>>>> mInterestingSubstitutions;

	public EMatching(QuantifierTheory quantifierTheory) {
		mQuantTheory = quantifierTheory;
		mTodoStack = new ArrayDeque<>();
		mInterestingSubstitutions = new HashMap<>();
		mUndoInformation = new HashMap<>();
	}

	public void addPatterns(final QuantLiteral qLit, final SourceAnnotation source) {
		final Collection<Term> patterns = new LinkedHashSet<>();

		final QuantLiteral qAtom = qLit.getAtom();
		if (qAtom instanceof QuantEquality) {
			final QuantEquality eq = (QuantEquality) qAtom;
			final Term lhs = eq.getLhs();
			// For EUTerm = EUTerm, add the two EUTerms to E-matching.
			// If one of them is an affine term of EUTerms, add all of them.
			// We also add the EUTerm in x = EUTerm.
			if (!(lhs instanceof TermVariable)) {
				final SMTAffineTerm lhsAff = new SMTAffineTerm(lhs);
				patterns.addAll(getSubPatterns(lhsAff));
			}
			final SMTAffineTerm rhsAff = new SMTAffineTerm(eq.getRhs());
			patterns.addAll(getSubPatterns(rhsAff));
		} else {
			// For (EUTerm <= 0) add all EU summands of the affine term of EUTerms on the lhs
			patterns.addAll(getSubPatterns(((QuantBoundConstraint) qAtom).getAffineTerm()));
		}
		if (!patterns.isEmpty()) {
			final Pair<ICode, CCTerm[]> newCode =
					new PatternCompiler(mQuantTheory, qLit, patterns.toArray(new Term[patterns.size()]), source)
							.compile();
			mTodoStack.add(newCode);
		}
	}

	private Collection<Term> getSubPatterns(final SMTAffineTerm at) {
		final Collection<Term> patterns = new LinkedHashSet<>();
		for (final Term smd : at.getSummands().keySet()) {
			if (!(smd instanceof TermVariable) && smd.getFreeVars().length != 0) {
				patterns.add(smd);
			}
		}
		return patterns;
	}

	/**
	 * Run E-matching. This executes the pieces of code currently on the stack.
	 * 
	 * TODO Find a good place to run E-Matching.
	 */
	public void run() {
		while (!mTodoStack.isEmpty()) {
			final Pair<ICode, CCTerm[]> code = mTodoStack.pop();
			code.getFirst().execute(code.getSecond());
		}
	}

	/**
	 * Undo everything that E-Matching did since the given decision level, i.e., remove triggers and interesting
	 * instantiations. This method must only be called after completely resolving a conflict.
	 * 
	 * TODO interesting instantiations?
	 * 
	 * @param decisionLevel
	 *            the current decision level.
	 */
	public void undo(int decisionLevel) {
		final Iterator<Entry<Integer, EMUndoInformation>> it = mUndoInformation.entrySet().iterator();
		while (it.hasNext()) {
			final Entry<Integer, EMUndoInformation> undo = it.next();
			if (undo.getKey() > decisionLevel) {
				undo.getValue().undo();
			}
			it.remove();
		}
	}

	/**
	 * Get the QuantifierTheory.
	 */
	public QuantifierTheory getQuantTheory() {
		return mQuantTheory;
	}

	/**
	 * Add code and a register as input to execute the code with.
	 * 
	 * @param code
	 *            the remaining code.
	 * @param register
	 *            the candidate CCTerms for this execution.
	 */
	void addCode(final ICode code, final CCTerm[] register) {
		mTodoStack.add(new Pair<ICode, CCTerm[]>(code, register));
	}

	/**
	 * Add a new interesting substitution for a quantified literal, together with the corresponding CCTerms.
	 * 
	 * @param qLit
	 *            the quantified Literal
	 * @param interestingSubs
	 *            the variable substitution
	 * @param candidates
	 *            the corresponding CCTerms for the EUTerms in the literal.
	 */
	void addInterestingSubstitution(final QuantLiteral qLit, final Map<Term, CCTerm> interestingSubs,
			final Map<Term, CCTerm> candidates) {
		if (!mInterestingSubstitutions.containsKey(qLit)) {
			mInterestingSubstitutions.put(qLit, new LinkedList<>());
		}
		mInterestingSubstitutions.get(qLit).add(new Pair<>(interestingSubs, candidates));
	}

	/**
	 * Install a trigger into the CClosure that compares two CCTerms.
	 * 
	 * @param lhs
	 *            the first CCTerm.
	 * @param rhs
	 *            the other CCTerm it should be compared with.
	 * @param remainingCode
	 *            the remaining E-Matching code.
	 * @param register
	 *            the candidate terms.
	 */
	void installCompareTrigger(final CCTerm lhs, final CCTerm rhs, final ICode remainingCode,
			final CCTerm[] register) {
		final EMCompareTrigger trigger = new EMCompareTrigger(this, remainingCode, register);
		mQuantTheory.getCClosure().insertCompareTrigger(lhs, rhs, trigger);
		addUndoInformation(trigger);
	}

	/**
	 * Install a trigger into the CClosure that finds function applications.
	 * 
	 * @param func
	 *            the function symbol.
	 * @param regIndex
	 *            the register index where the function application is to be stored.
	 * @param remainingCode
	 *            the remaining E-Matching code.
	 * @param register
	 *            the candidate terms.
	 */
	void installFindTrigger(final FunctionSymbol func, final int regIndex, final ICode remainingCode,
			final CCTerm[] register) {
		final EMReverseTrigger trigger = new EMReverseTrigger(this, remainingCode, register, regIndex);
		mQuantTheory.getCClosure().insertReverseTrigger(func, trigger);
		addUndoInformation(trigger);
	}

	/**
	 * Install a trigger into the CClosure that finds function applications with a given argument.
	 * 
	 * @param func
	 *            the function symbol.
	 * @param arg
	 *            the argument the function application should contain.
	 * @param argPos
	 *            the position of the given argument.
	 * @param regIndex
	 *            the register index where the function application is to be stored.
	 * @param remainingCode
	 *            the remaining E-Matching code.
	 * @param register
	 *            the candidate terms.
	 */
	void installReverseTrigger(final FunctionSymbol func, final CCTerm arg, final int argPos,
			final int regIndex, final ICode remainingCode, final CCTerm[] register) {
		final EMReverseTrigger trigger = new EMReverseTrigger(this, remainingCode, register, regIndex);
		mQuantTheory.getCClosure().insertReverseTrigger(func, arg, argPos, trigger);
		addUndoInformation(trigger);
	}

	private void addUndoInformation(final EMCompareTrigger trigger) {
		final int decisionLevel = mQuantTheory.getClausifier().getEngine().getDecideLevel();
		if (!mUndoInformation.containsKey(decisionLevel)) {
			mUndoInformation.put(decisionLevel, new EMUndoInformation());
		}
		final EMUndoInformation info = mUndoInformation.get(decisionLevel);
		info.mCompareTriggers.add(trigger);
	}

	private void addUndoInformation(final EMReverseTrigger trigger) {
		final int decisionLevel = mQuantTheory.getClausifier().getEngine().getDecideLevel();
		if (!mUndoInformation.containsKey(decisionLevel)) {
			mUndoInformation.put(decisionLevel, new EMUndoInformation());
		}
		final EMUndoInformation info = mUndoInformation.get(decisionLevel);
		info.mReverseTriggers.add(trigger);
	}

	/**
	 * This class stores information about which steps in the E-Matching process we have to undo after backtracking.
	 * 
	 * @author Tanja Schindler
	 */
	class EMUndoInformation {
		final Collection<EMCompareTrigger> mCompareTriggers;
		final Collection<EMReverseTrigger> mReverseTriggers;

		EMUndoInformation() {
			mCompareTriggers = new ArrayList<>();
			mReverseTriggers = new ArrayList<>();
		}

		/**
		 * Undo every E-Matching step stored in this undo information.
		 */
		void undo() {
			for (final EMCompareTrigger trigger : mCompareTriggers) {
				mQuantTheory.getCClosure().removeCompareTrigger(trigger);
			}
			for (final EMReverseTrigger trigger : mReverseTriggers) {
				mQuantTheory.getCClosure().removeReverseTrigger(trigger);
			}
		}
	}
}
