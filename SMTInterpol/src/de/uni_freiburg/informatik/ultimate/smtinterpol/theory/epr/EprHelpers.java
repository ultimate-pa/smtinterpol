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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.AbstractDawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgLetterFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DeterministicDawgTransitionRelation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.EmptyDawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.HashRelation3;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.PairDawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.Triple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.IEprLiteral;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EprHelpers {

	/**
	 * Goes through all the given literals 
	 * and adds all appearing constants to mAppearingConstants
	 */
	public static HashSet<ApplicationTerm> collectAppearingConstants(Literal[] literals, Theory theory) {
		HashSet<ApplicationTerm> result = new HashSet<ApplicationTerm>();
		for (Literal l : literals) {
			DPLLAtom atom = (DPLLAtom) l.getAtom();
			Term t = atom.getSMTFormula(theory);
			if (!(t instanceof ApplicationTerm)) {
				continue;
			}
			if (!(atom instanceof EprAtom || atom instanceof CCEquality)) {
				continue;
			}
			for (Term p : ((ApplicationTerm) t).getParameters()) {
				if (p instanceof ApplicationTerm) {
					assert ((ApplicationTerm) p).getFunction().getParameterSorts().length == 0;
					result.add((ApplicationTerm) p);
				}
			}
		}
		return result;
	}	
	
	public static Literal applySubstitution(TTSubstitution sub, Literal l, EprTheory eprTheory) {
		return applySubstitution(sub, l, eprTheory, false);
	}
	/**
	 * Apply the substitution sub to Literal l, return the result
	 * @param sub
	 * @param l
	 * @param theory
	 * @param calledFromDER the DER-case is special if we are in completeGroundingMode
	 * @return
	 */
	public static Literal applySubstitution(TTSubstitution sub, Literal l, EprTheory eprTheory, boolean calledFromDER) {
		boolean isPositive = l.getSign() == 1;
		DPLLAtom atom = l.getAtom();
		
		Theory theory = eprTheory.getTheory();

		Literal resultLit = null;
		DPLLAtom resultAtom = null;
		
		if (atom instanceof EprQuantifiedPredicateAtom) {
			EprQuantifiedPredicateAtom eqpa = (EprQuantifiedPredicateAtom) atom;
			TermTuple newTT = sub.apply(eqpa.getArgumentsAsTermTuple());

			resultAtom = eqpa.getEprPredicate().getAtomForTermTuple(newTT, theory, eprTheory.getClausifier().getStackLevel());
		} else if (atom instanceof EprQuantifiedEqualityAtom) {
			EprQuantifiedEqualityAtom eea = (EprQuantifiedEqualityAtom) atom;
			TermTuple newTT = sub.apply(eea.getArgumentsAsTermTuple());
			ApplicationTerm newTerm = theory.term("=", newTT.terms);
			
			if (newTerm.getFreeVars().length > 0) {
				resultAtom = new EprQuantifiedEqualityAtom(newTerm, 0, l.getAtom().getAssertionStackLevel());//TODO: hash
			} else {
				// TODO: will need a management for these atoms -- so there are no duplicates..
				//   it's not clear if we want CCEqualities or so, here..
				int assertionStackLevel = eprTheory.getClausifier().getStackLevel();
				resultAtom =  new EprGroundEqualityAtom(newTerm, 0, assertionStackLevel);
			}
		} else {
			//assert false : "there might be equality replacements"; --> seems idiotic now..
			// literal is ground, just return it
			return l;
		}
		
		
		if (EprTheorySettings.FullInstatiationMode) {
			// we are in the mode where Epr just computes all the groundings of each
			// quantified formula
			// --> thus EprAtoms must become CCEqualities
			Clausifier clausif = eprTheory.getClausifier();
			if (resultAtom instanceof EprGroundPredicateAtom) {
				// basically copied from Clausifier.createBooleanLit()
				SharedTerm st = clausif.getSharedTerm(((EprGroundPredicateAtom) resultAtom).getTerm());

				EqualityProxy eq = clausif.
						createEqualityProxy(st, clausif.getSharedTerm(eprTheory.getTheory().mTrue));
				// Safe since m_Term is neither true nor false
				assert eq != EqualityProxy.getTrueProxy();
				assert eq != EqualityProxy.getFalseProxy();
				resultAtom = eq.getLiteral();	
			} else if (resultAtom instanceof EprGroundEqualityAtom) {
				Term t1 = ((EprAtom) resultAtom).getArguments()[0];
				Term t2 = ((EprAtom) resultAtom).getArguments()[1];
				if (t1.equals(t2)) {
					resultAtom = new DPLLAtom.TrueAtom();
				} else {
					SharedTerm st1 = clausif.getSharedTerm(((EprAtom) resultAtom).getArguments()[0]);
					SharedTerm st2 = clausif.getSharedTerm(((EprAtom) resultAtom).getArguments()[1]);
					EqualityProxy eq = new EqualityProxy(clausif, 
							st1, 
							st2);
					resultAtom = eq.getLiteral();
				}
			} else {
				assert calledFromDER : "not called from DER, but not ground, as it looks"
						+ " -- should not happen, right??";
			}
		}
		resultLit =  isPositive ? resultAtom : resultAtom.negate();
		return resultLit;
	}

	/**
	 * sub is a unifier for the predicateAtoms in setEqlwe and clauseLit.
	 * Apply sub to the equalities in setEqlwe and eprEqualityAtoms,
	 * return the result as a clause.
	 * @param setEqlwe
	 * @param clauseLit
	 * @param eprEqualityAtoms
	 * @param sub
	 * @return
	 */
	public static Literal[] applyUnifierToEqualities(EprQuantifiedEqualityAtom[] eprEqualityAtoms1,
			EprQuantifiedEqualityAtom[] eprEqualityAtoms2, TTSubstitution sub, EprTheory eprTheory) {
		
		ArrayList<Literal> result = new ArrayList<Literal>();
		for (EprQuantifiedEqualityAtom eea : eprEqualityAtoms1) 
			result.add(EprHelpers.applySubstitution(sub, eea, eprTheory));
		for (EprQuantifiedEqualityAtom eea : eprEqualityAtoms2)
			result.add(EprHelpers.applySubstitution(sub, eea, eprTheory));

		return result.toArray(new Literal[result.size()]);
	}
	
	public static ArrayList<DPLLAtom> substituteInExceptions(
			EprQuantifiedEqualityAtom[] equalities, TTSubstitution sub, EprTheory eprTheory) {
		
		ArrayList<DPLLAtom> result = new ArrayList<DPLLAtom>();
		for (EprQuantifiedEqualityAtom eea : equalities) {
			result.add((DPLLAtom) EprHelpers.applySubstitution(sub, eea, eprTheory));
		}
		return result;
	}
	
//	public static class Pair<T,U> {
//		public final T first;
//		public final U second;
//		
//		public Pair(T f, U s) {
//			first = f;
//			second = s;
//		}
//	}

	/**
	 * When we are sure (or want to be sure) that a Term array really only contains constants, 
	 * we make the cast using this method.
	 * @param arguments
	 * @return
	 */
	public static ApplicationTerm[] castTermsToConstants(Term[] arguments) {
		ApplicationTerm[] ats = new ApplicationTerm[arguments.length];
		for (int i = 0; i < arguments.length; i++) {
			assert arguments[i] instanceof ApplicationTerm &&
			   ((ApplicationTerm) arguments[i]).getParameters().length == 0 
			   : "This method should only be called on arrays of constants";
			ats[i] = (ApplicationTerm) arguments[i];
		}
		return ats;
	}
	
	/**
	 * Given a set S, computes S x S ... x S = S^n
	 */
	public static <LETTER> Set<List<LETTER>> computeNCrossproduct(Set<LETTER> baseSet, int n, LogProxy logger) {
//		logger.debug("EPRDEBUG: EprHelpers.computeNCrossproduct N = " + n + " baseSet size = " + baseSet.size());
		Set<List<LETTER>> result = new HashSet<List<LETTER>>();
		result.add(new ArrayList<LETTER>());
		for (int i = 0; i < n; i++) {
			Set<List<LETTER>> newResult = new HashSet<List<LETTER>>();
			for (List<LETTER> tuple : result) {
				for (LETTER ltr : baseSet) {
					List<LETTER> newTuple = new ArrayList<LETTER>(tuple);
					newTuple.add(ltr);
					newResult.add(newTuple);
				}
			}
			result = newResult;
		}
		return result;
	}
	
//	public class EprClauseIterable implements Iterable<EprClause> {
//
//		Iterator<EprPushState> mPushStateStack;
//
//		public EprClauseIterable(Stack<EprPushState> pushStateStack) {
//			mPushStateStack = pushStateStack.iterator();
//		}
//
//		@Override
//		public Iterator<EprClause> iterator() {
//			return new EprClauseIterator();
//		}
//
//		class EprClauseIterator implements Iterator<EprClause> {
//			EprClause mNext;
//			Iterator<EprClause> mCurrentPushStateClauseIterator;
//
//			EprClauseIterator() {
//				mNext = findNextEprClause();
//			}
//
//			public EprClause findNextEprClause() {
//				if (! mPushStateStack.hasNext()) {
//					return null;
//				}
//				mCurrentPushStateClauseIterator = mPushStateStack.next().getClausesIterator();
//
//				// look for the first push state that has a clause
//				while (! mCurrentPushStateClauseIterator.hasNext()) {
//					if (!mPushStateStack.hasNext()) {
//						return null;
//					}
//					mCurrentPushStateClauseIterator = mPushStateStack.next().getClausesIterator();
//				}
//				return mCurrentPushStateClauseIterator.next();
//			}
//
//			@Override
//			public boolean hasNext() {
//				return mNext != null;
//			}
//
//			@Override
//			public EprClause next() {
//				mNext = findNextEprClause();
//				return mNext;
//			}
//		}
//	}
//	
//	public class DecideStackLiteralIterable implements Iterable<DecideStackLiteral> {
//
//		Iterator<EprPushState> mPushStateStack;
//
//		public DecideStackLiteralIterable(Stack<EprPushState> pushStateStack) {
//			mPushStateStack = pushStateStack.iterator();
//		}
//
//		@Override
//		public Iterator<DecideStackLiteral> iterator() {
//			return new DSLIterator();
//		}
//
//		class DSLIterator implements Iterator<DecideStackLiteral> {
//			DecideStackLiteral mNext;
//			Iterator<DecideStackLiteral> mCurrentPushStateClauseIterator;
//
//			DSLIterator() {
//				mNext = findNextEprClause();
//			}
//
//			public DecideStackLiteral findNextEprClause() {
//				if (! mPushStateStack.hasNext()) {
//					return null;
//				}
//				mCurrentPushStateClauseIterator = mPushStateStack.next().getDecideStackLiteralIterator();
//
//				// look for the first push state that has a clause
//				while (! mCurrentPushStateClauseIterator.hasNext()) {
//					if (!mPushStateStack.hasNext()) {
//						return null;
//					}
//					mCurrentPushStateClauseIterator = mPushStateStack.next().getDecideStackLiteralIterator();
//				}
//				return mCurrentPushStateClauseIterator.next();
//			}
//
//			@Override
//			public boolean hasNext() {
//				return mNext != null;
//			}
//
//			@Override
//			public DecideStackLiteral next() {
//				mNext = findNextEprClause();
//				return mNext;
//			}
//		}
//	}

	public static <COLNAMES> COLNAMES[] applyMapping(
			COLNAMES[] colnames, Map<COLNAMES, COLNAMES> translation) {
		assert colnames.length > 0;
		COLNAMES[] result = colnames.clone();
		for (int i = 0; i < colnames.length; i++) {
			COLNAMES newEntry = translation.get(colnames[i]);
			if (newEntry != null) {
				result[i] = newEntry;
			}
		}
		return result;
	}
	
	public static <COLNAMES> List<COLNAMES> applyMapping(
			List<COLNAMES> colnames, Map<COLNAMES, COLNAMES> translation) {
		assert colnames.size() > 0;
		List<COLNAMES> result = new ArrayList<COLNAMES>();
		for (COLNAMES cn : colnames) {
			COLNAMES newEntry = translation.get(cn);
			if (newEntry != null) {
				result.add(newEntry);
			} else {
				result.add(cn);
			}
		}
		return result;
	}
	
	public static <COLNAMES> SortedSet<COLNAMES> applyMapping(
			SortedSet<COLNAMES> colnames, Map<COLNAMES, COLNAMES> translation) {
		assert colnames.size() > 0;
		SortedSet<COLNAMES> result = new TreeSet<COLNAMES>(EprHelpers.getColumnNamesComparator());
		for (COLNAMES cn : colnames) {
			COLNAMES newEntry = translation.get(cn);
			if (newEntry != null) {
				result.add(newEntry);
			} else {
				result.add(cn);
			}
		}
		return result;
	}
	public static List<ApplicationTerm> convertTermListToConstantList(List<Term> constants) {
	    List<ApplicationTerm> result = new ArrayList<ApplicationTerm>(constants.size());
		for (Term t : constants) {
			result.add((ApplicationTerm) t);
		}
		return result;
	}

	public static List<ApplicationTerm> convertTermArrayToConstantList(Term[] constants) {
	    List<ApplicationTerm> result = new ArrayList<ApplicationTerm>(constants.length);
		for (int i = 0; i < constants.length; i++) {
			result.add((ApplicationTerm) constants[i]);
		}
		return result;
	}

	public static boolean haveSameSignature(IDawg<ApplicationTerm, TermVariable>... dawgs) {
		for (IDawg<ApplicationTerm, TermVariable> d1 : dawgs) {
			for (IDawg<ApplicationTerm, TermVariable> d2 : dawgs) {
				if (! d1.getColNames().equals(d2.getColNames())) {
						return false;
				}
			}
		}
		return true;
	}
	
	/**
	 * Provides a Comparator for the SortedSets we use for the dawg signatures.
	 * TODO: we really only need one instance of this.. (but what was the best way to have a singleton again?..)
	 * @return
	 */
	public static <COLNAMES> Comparator<COLNAMES> getColumnNamesComparator() {
		return ColNameComparator.getInstance();
	}
	
	static class ColNameComparator<COLNAMES> implements Comparator<COLNAMES> {

		private static ColNameComparator instance = new ColNameComparator();

		private ColNameComparator() {
		}
		
		@SuppressWarnings("unchecked")
		public static <COLNAMES> ColNameComparator<COLNAMES> getInstance() {
			return instance;
		}

		@Override
		public int compare(COLNAMES o1, COLNAMES o2) {
			// we can only deal with TermVariables and Strings right now --> otherwise this will throw an exception...
			if (o1 instanceof TermVariable) {
				TermVariable tv1 = (TermVariable) o1;
				TermVariable tv2 = (TermVariable) o2;
				return tv1.getName().compareTo(tv2.getName());
			} else if (o1 instanceof String) {
				return ((String) o1).compareTo((String) o2);
			} else if (o1 instanceof Integer) {
				return ((Integer) o1).compareTo((Integer) o2);
			}

			throw new UnsupportedOperationException("unexpected comparator call");
//			return o1.toString().compareTo(o2.toString());//might work for all..
		}
		
	}

	public static <COLNAMES> Map<COLNAMES, Integer> computeColnamesToIndex(SortedSet<COLNAMES> sortedSet) {
		Map<COLNAMES, Integer> result = new HashMap<COLNAMES, Integer>();
		
		Iterator<COLNAMES> sortedSetIt = sortedSet.iterator();
		for (int i = 0; i < sortedSet.size(); i++) {
			COLNAMES ithElement = sortedSetIt.next();
			result.put(ithElement, i);
		}
		return result;
	}
	/**
	 * Computes all the instantiations of the variables in freeVars that
	 * are added to the set of instantiations of oldConstants by adding one
	 * or more constants from newConstants.
	 * In other words: compute all instantiations of freeVars where a new constant occurs
	 * at least once.
	 * 
	 * @param freeVars
	 * @param newConstant
	 * @param oldConstants
	 * @return
	 */
	public static ArrayList<TTSubstitution> getAllInstantiationsForNewConstant(
			Set<TermVariable> freeVars, 
			Set<ApplicationTerm> newConstants,
			Set<ApplicationTerm> oldConstants) {
		
		ArrayList<TTSubstitution> instsWithNewConstant = 
				new ArrayList<TTSubstitution>();
		ArrayList<TTSubstitution> instsWithOutNewConstant = 
				new ArrayList<TTSubstitution>();
		
		HashSet<ApplicationTerm> allConstants = new HashSet<ApplicationTerm>(oldConstants);
		allConstants.addAll(newConstants);

		instsWithNewConstant.add(new TTSubstitution());
		instsWithOutNewConstant.add(new TTSubstitution());

		for (TermVariable tv : freeVars) {
			ArrayList<TTSubstitution> instsNewWNC = new ArrayList<TTSubstitution>();
			ArrayList<TTSubstitution> instsNewWONC = new ArrayList<TTSubstitution>();
			for (TTSubstitution sub : instsWithNewConstant) {
				for (ApplicationTerm con : allConstants) {
					if (con.getSort().getRealSort() == tv.getSort().getRealSort()) {
						TTSubstitution newSub = new TTSubstitution(sub);
						newSub.addSubs(con, tv);
						instsNewWNC.add(newSub);
					}
				}
			}

			for (TTSubstitution sub : instsWithOutNewConstant) {
				for (ApplicationTerm con : oldConstants) {
					if (con.getSort().equals(tv.getSort())) {
						TTSubstitution newSub = new TTSubstitution(sub);
						newSub.addSubs(con, tv);
						instsNewWONC.add(newSub);
					}
				}
				for (ApplicationTerm newConstant : newConstants) {
					if (newConstant.getSort().equals(tv.getSort())) {
						TTSubstitution newSub = new TTSubstitution(sub);
						newSub.addSubs(newConstant, tv);
						instsNewWNC.add(newSub);
					}
				}
			}
			instsWithNewConstant = instsNewWNC;
			instsWithOutNewConstant = instsNewWONC;
		}
		return instsWithNewConstant;
	}

	public static ArrayList<TTSubstitution> getAllInstantiations(
			Set<TermVariable> freeVars, 
			Set<ApplicationTerm> constants) {
		ArrayList<TTSubstitution> insts = new ArrayList<TTSubstitution>();
		insts.add(new TTSubstitution());

		for (TermVariable tv : freeVars) {
			ArrayList<TTSubstitution> instsNew = new ArrayList<TTSubstitution>();
			for (TTSubstitution sub : insts) {
				for (ApplicationTerm con : constants) {
					if (con.getSort().getRealSort() == tv.getSort().getRealSort()) {
						TTSubstitution newSub = new TTSubstitution(sub);
						newSub.addSubs(con, tv);
						instsNew.add(newSub);
					}
				}
			}
			insts = instsNew;
		}
		return insts;
	}
	
	
	/**
	 * Checks if the sort of the entries of the points match the sort of their columns
	 * @param point
	 * @param colnames
	 * @return
	 */
	public static <LETTER, COLNAMES> boolean verifySortsOfPoints(Iterable<List<LETTER>> points, SortedSet<COLNAMES> colnames) {
		for (List<LETTER> point : points) {
			if (!verifySortsOfPoint(point, colnames)) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Checks if the sort of the entries of the point match the sort of their columns
	 * @param point
	 * @param colnames
	 * @return
	 */
	public static <LETTER, COLNAMES> boolean verifySortsOfPoint(List<LETTER> point, SortedSet<COLNAMES> colnames) {
		if (point.size() == 0) {
			return true;
		}
		if (!(point.get(0) instanceof ApplicationTerm)
				|| !(colnames.iterator().next() instanceof TermVariable)) {
			// this method only applies if Colnames is TermVariable and Letter is ApplicationTerm
			return true;
		}
		Iterator<COLNAMES> colnamesIt = colnames.iterator();
		for (int i = 0; i< point.size(); i++) {
			ApplicationTerm pointAtI = (ApplicationTerm) point.get(i);
			TermVariable colnameTvI = (TermVariable) colnamesIt.next();
			
			if (pointAtI.getSort().getRealSort() != colnameTvI.getSort().getRealSort()) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Checks if, given the contained literal's decide statuses, if the given
	 * clause is currently a unit claus with the given literal as unit literal.
	 * This is the variant where we expect that the unit literal is (still) fulfilled.
	 * @param reason
	 * @param l
	 * @return
	 */
	public static boolean verifyUnitClauseAfterPropagation(Clause reason, Literal l, LogProxy logger) {
		return verifyUnitClause(reason, l, true, null, logger);
	}
	
	/**
	 * Checks if, given the contained literal's decide statuses, if the given
	 * clause is currently a unit claus with the given literal as unit literal.
	 * This is the variant where we expect that the unit literal is (still) undecided.
	 */
	public static boolean verifyUnitClauseBeforePropagation(Clause reason, Literal l, LogProxy logger) {
		return verifyUnitClause(reason, l, false, null, logger);
	}

	public static boolean verifyUnitClause(Clause reason, Literal l, boolean afterPropagation, 
			Deque<Literal> literalsWaitingToBePropagated, LogProxy logger) {
		for (int i = 0; i < reason.getSize(); i++) {
			Literal curLit = reason.getLiteral(i);
			if (curLit == l) {
				if (afterPropagation && curLit.getAtom().getDecideStatus() != curLit) {
					logger.error("EPRDEBUG: (EprHelpers.verifyUnitClause): The unit literal " + l + " is not set.");
					return false;
				} else if  (!afterPropagation && curLit.getAtom().getDecideStatus() != null) {
					logger.error("EPRDEBUG: (EprHelpers.verifyUnitClause): The unit literal " + l + " is not undecided.");
					return false;
				}
			} else {
				//curLit != l

				boolean refutedInDPLLEngine = curLit.getAtom().getDecideStatus() == curLit.negate();
				boolean refutationQueuedForPropagation = literalsWaitingToBePropagated != null 
						&& literalsWaitingToBePropagated.contains(curLit.negate());
						
				if (!refutedInDPLLEngine && !refutationQueuedForPropagation) {
					logger.error("EPRDEBUG: (EprHelpers.verifyUnitClause): Literal " + curLit + 
							" is not the unit literal but is not currently refuted");
					return false;
				}
			}
		}
		return true;
	}

	public static boolean verifyConflictClause(Clause conflict, LogProxy logger) {
		if (conflict == null) {
			return true;
		}
		for (int i = 0; i < conflict.getSize(); i++) {
			Literal curLit = conflict.getLiteral(i);
			if (curLit.getAtom().getDecideStatus() != curLit.negate()) {
				logger.error("EPRDEBUG: (EprHelpers.verifyConflictClause): Literal " + curLit + 
						" is not currently refuted");
				return false;
			}
		}
		return true;
	}

	public static boolean verifyUnitClauseAtEnqueue(Literal l, Clause reason,
			Deque<Literal> mLiteralsWaitingToBePropagated, LogProxy logger) {
//		for (int i = 0; i < reason.getSize(); i++) {
//			Literal curLit = reason.getLiteral(i);
//			
//			if (curLit == l) {
//				if (afterPropagation && curLit.getAtom().getDecideStatus() != curLit) {
//					logger.error("EPRDEBUG: (EprHelpers.verifyUnitClause): The unit literal " + l + " is not set.");
//					return false;
//				} else if  (!afterPropagation && curLit.getAtom().getDecideStatus() != null) {
//					logger.error("EPRDEBUG: (EprHelpers.verifyUnitClause): The unit literal " + l + " is not undecided.");
//					return false;
//				}
//			}
//			if (curLit != l && curLit.getAtom().getDecideStatus() != curLit.negate()) {
//				logger.error("EPRDEBUG: (EprHelpers.verifyUnitClause): Literal " + curLit + 
//						" is not the unit literal but is not currently refuted");
//				return false;
//			}
//
//		}

		return verifyUnitClause(reason, l, false, mLiteralsWaitingToBePropagated, logger);
	}

	public static boolean verifyThatDpllAndEprDecideStackAreConsistent(ScopedHashSet<EprPredicate> allEprPredicates, LogProxy logger) {
		boolean result = true;
		for (EprPredicate pred : allEprPredicates) {
			for (IEprLiteral el : pred.getEprLiterals()) {
				for (EprGroundPredicateAtom at : pred.getDPLLAtoms()) {
					List<ApplicationTerm> atArgs = convertTermArrayToConstantList(at.getArguments());
					if (!el.getDawg().accepts(atArgs)) {
						// different arguments
						continue;
					}
					// arguments match

					if (at.getDecideStatus() == null) {
						logger.debug("EPRDEBUG: EprHelpers.verify..DpllAndEprDecideStack..: DPLLEngine: " + at + 
								" undecided; EprTheory: " + at + " is set with polarity " + el.getPolarity());
						result = false;
						continue;
					}

					if ((at.getDecideStatus().getSign() == 1) != el.getPolarity()) {
						logger.debug("EPRDEBUG: EprHelpers.verifyThatDpllAndEprDecideStackAreConsistent: DPLLEngine: " + at + 
								" is set with polarity " + at.getSign() == 1 + 
								"; EprTheory: " + at + " is set with polarity " + el.getPolarity());
						result = false;
					}
				}
			}
		}
		return result;
	}
	/**
	 * Transforms a signature according to the given translation.
	 * <p>
	 * The translation is a map from  column names in the old signature to sets of column names in the new signature.
	 * If a column name in the old signature is not mentioned in the translation, it is left unchanged (thus will
	 * occur in the new signature).
	 * If an "old" column name is mapped to more than one column name, the "old" column name is removed and the new ones
	 * are added to the new signature.
	 * 
	 * @param colNames
	 * @param renaming
	 * @return
	 */
	public static <COLNAMES> SortedSet<COLNAMES> transformSignature(final SortedSet<COLNAMES> colNames,
			final BinaryRelation<COLNAMES, COLNAMES> renaming) {
		final SortedSet<COLNAMES> result = new TreeSet<COLNAMES>(EprHelpers.getColumnNamesComparator());
		for (COLNAMES oldCol : colNames) {
			final Set<COLNAMES> newCols = renaming.getImage(oldCol);
			if (newCols == null) {
				result.add(oldCol);
			}
			for (COLNAMES newCol : newCols) {
				result.add(newCol);
			}
		}
		return result;
	}

	/**
	 * Transforms a signature according to the given translation.
	 * <p>
	 * The translation is a map from column names in the old signature to column names in the new signature.
	 * If a column name in the old signature is not mentioned in the translation, it is left unchanged (thus will
	 * occur in the new signature).
	 * 
	 * @param colNames
	 * @param renaming
	 * @return
	 */
	public static <COLNAMES> SortedSet<COLNAMES> transformSignature(final SortedSet<COLNAMES> colNames,
			final Map<COLNAMES, COLNAMES> renaming) {
		final SortedSet<COLNAMES> result = new TreeSet<COLNAMES>(EprHelpers.getColumnNamesComparator());
		for (COLNAMES oldCol : colNames) {
			final COLNAMES newCol = renaming.get(oldCol);
			if (newCol == null) {
				result.add(oldCol);
			} else {
				result.add(newCol);
			}
		}
		return result;
	}
	
	/**
	 * Returns true iff in this dawg all the outgoing dawgLetters of one state are disjoint.
	 * @param transitionRelation 
	 * @return
	 */
	public static <LETTER, COLNAMES> boolean isDeterministic(
			DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> transitionRelation) {
		for (DawgState state : transitionRelation.keySet()) {
			List<Pair<IDawgLetter<LETTER, COLNAMES>, DawgState>> outEdges = 
					new ArrayList<Pair<IDawgLetter<LETTER, COLNAMES>, DawgState>>(transitionRelation.getOutEdgeSet(state));
			for (int i = 0; i < outEdges.size(); i++) {
				Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> edge1 = outEdges.get(i);
				for (int j = 0; j < i; j++) {
					Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> edge2 = outEdges.get(j);
					
					if (!(edge1.getFirst().intersect(edge2.getFirst()) instanceof EmptyDawgLetter)) {
						return false;
					}
				}
			}
		}
		return true;
	}
	
	
	/**
	 * Checks for a given transition relation and dawg state (usually the initial state of the dawg
	 * the transition relation occurs) if every transition in the relation is reachable from the state
	 * (in the normal direction, no backwards search is done)
	 * 
	 * @param transitionRelation
	 * @return
	 */
	public static <LETTER, COLNAMES> boolean hasDisconnectedTransitions(
			DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> transitionRelation,
			DawgState state) {
		
		final Set<Triple<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState>> reachableTransitions = 
				new HashSet<Triple<DawgState,IDawgLetter<LETTER,COLNAMES>,DawgState>>();
		
		Set<DawgState> currentStates = new HashSet<DawgState>();
		currentStates.add(state);
		
		while (!currentStates.isEmpty()) {
			final Set<DawgState> nextStates = new HashSet<DawgState>();
			for (DawgState cs : currentStates) {
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outEdge : transitionRelation.getOutEdgeSet(cs)) {
					nextStates.add(outEdge.getSecond());
					reachableTransitions.add(
							new Triple<DawgState, IDawgLetter<LETTER,COLNAMES>, DawgState>(
									cs, outEdge.getFirst(), outEdge.getSecond()));
				}
			}
			currentStates = nextStates;
		}

		final Iterable<Triple<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState>> allTransitions = 
				transitionRelation.entrySet();
		for (Triple<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> trans : allTransitions) {
			if (!reachableTransitions.contains(trans)) {
				return true;
			}
		}
		return false;
	}

	public static <LETTER, COLNAMES> boolean areStatesUnreachable(
			DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> transitionRelation,
			DawgState initialState,
			Set<PairDawgState> statesToCheck) {

		final Set<DawgState> statesNotYetShownReachable = new HashSet<DawgState>(statesToCheck);		

		Set<DawgState> currentStates = new HashSet<DawgState>();
		currentStates.add(initialState);
		statesNotYetShownReachable.remove(initialState);
		
		while (!currentStates.isEmpty()) {
			final Set<DawgState> nextStates = new HashSet<DawgState>();
			for (DawgState cs : currentStates) {
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outEdge : transitionRelation.getOutEdgeSet(cs)) {
					statesNotYetShownReachable.remove(outEdge.getSecond());
					nextStates.add(outEdge.getSecond());
				}
			}
			currentStates = nextStates;
		}

		if (statesNotYetShownReachable.isEmpty()) {
			return false;
		} else {
			return true;
		}
	}
	
	
	/**
	 * The input DawgStates are to be merged into one SetDawgState.
	 * Problem: their outgoing DawgLetters may partially overlap.
	 * 
	 * This methods splits all the outgoing dawgLetters into sub-DawgLetters that are disjoint. 
	 * Its result associates every outgoing DawgLetter with a set of subdawgLetters that are 
	 * disjoint (or identical) to the outgoing DawgLetters of all other states in the input set.
	 * @param dawgLetterFactory 
	 * 
	 * @param dawgStates
	 * @param transitionRelation 
	 * @return
	 */
	public static <LETTER, COLNAMES> BinaryRelation<IDawgLetter<LETTER, COLNAMES>, IDawgLetter<LETTER, COLNAMES>> divideDawgLetters(
			DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory, 
			Set<DawgState> dawgStates, 
			HashRelation3<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> transitionRelation) {
		

		
		final Set<IDawgLetter<LETTER, COLNAMES>> allOutgoingDawgLetters = new HashSet<IDawgLetter<LETTER,COLNAMES>>();
		for (DawgState source : transitionRelation.projectToFst()) {
			for (IDawgLetter<LETTER, COLNAMES> letter : transitionRelation.projectToSnd(source)) {
				for (DawgState target : transitionRelation.projectToTrd(source, letter)) {
					allOutgoingDawgLetters.add(letter);
				}
			}
		}
		return divideDawgLetters(dawgLetterFactory, dawgStates, allOutgoingDawgLetters);
	}
	
	
	/**
	 * Variant of this method used by union (instead of deteminization)
	 * 
	 * @param dawgLetterFactory 
	 * 
	 * @param dawgStates
	 * @param firstTransitionRelation 
	 * @return 
	 * @return
	 */
	public static <LETTER, COLNAMES>  BinaryRelation<IDawgLetter<LETTER, COLNAMES>, IDawgLetter<LETTER, COLNAMES>> 
				divideDawgLetters(DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory, 
			DawgState first,
			DawgState second,
			DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> firstTransitionRelation,
			DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> secondTransitionRelation) {
		
		final Set<DawgState> dawgStates = new HashSet<DawgState>();
		dawgStates.add(first);
		dawgStates.add(second);

//		final Set<IDawgLetter<LETTER, COLNAMES>> allOutgoingDawgLetters = new HashSet<IDawgLetter<LETTER,COLNAMES>>();
//		for (Triple<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> edge : firstTransitionRelation.entrySet()) {
//					allOutgoingDawgLetters.add(edge.getSecond());
//		}
//		for (Triple<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> edge : secondTransitionRelation.entrySet()) {
//					allOutgoingDawgLetters.add(edge.getSecond());
//		}
		final Set<IDawgLetter<LETTER, COLNAMES>> allOutgoingDawgLetters = new HashSet<IDawgLetter<LETTER,COLNAMES>>();
		for (Entry<IDawgLetter<LETTER, COLNAMES>, DawgState> edge : firstTransitionRelation.get(first).entrySet()) {
			allOutgoingDawgLetters.add(edge.getKey());
		}
		for (Entry<IDawgLetter<LETTER, COLNAMES>, DawgState> edge : secondTransitionRelation.get(second).entrySet()) {
			allOutgoingDawgLetters.add(edge.getKey());
		}
	
		return divideDawgLetters(dawgLetterFactory, dawgStates, allOutgoingDawgLetters);
	}
		
	private static <LETTER, COLNAMES> BinaryRelation<IDawgLetter<LETTER, COLNAMES>, IDawgLetter<LETTER, COLNAMES>> divideDawgLetters(
			DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory, 
			Set<DawgState> dawgStates, 
			Set<IDawgLetter<LETTER, COLNAMES>> allOutgoingDawgLetters) {
		/*
		 * In this relation we keep the mapping between the original states and the (partially) split states.
		 */
		final BinaryRelation<IDawgLetter<LETTER, COLNAMES>, IDawgLetter<LETTER, COLNAMES>> result = 
				new BinaryRelation<IDawgLetter<LETTER,COLNAMES>, IDawgLetter<LETTER,COLNAMES>>();
	
		for (IDawgLetter<LETTER, COLNAMES> letter : allOutgoingDawgLetters) {
					result.addPair(letter, letter);
		}

		/*
		 * algorithmic plan:
		 *  worklist algorithm where the worklist is the set of letters
		 *  in each iteration: 
		 *   - search for two intersecting letters l1, l2, break if there are none
		 *   - remove l1, l2, add the letters l1\l2, l1 \cap l2, l2\l1 to the worklist
		 */
		Set<IDawgLetter<LETTER, COLNAMES>> worklist = new HashSet<IDawgLetter<LETTER, COLNAMES>>(allOutgoingDawgLetters);
		while (true) {
			Pair<IDawgLetter<LETTER, COLNAMES>, IDawgLetter<LETTER, COLNAMES>> intersectingPair = 
					findIntersectingPair(dawgLetterFactory, worklist);
			if (intersectingPair == null) {
				// all DawgLetters in worklist are pairwise disjoint or identical --> we're done
				break;
			}
			worklist.remove(intersectingPair.getFirst());
			worklist.remove(intersectingPair.getSecond());
			
			assert intersectingPair.getFirst().getSortId().equals(intersectingPair.getSecond().getSortId());
			

			/*
			 * update the worklist
			 */
			final IDawgLetter<LETTER, COLNAMES> intersection = intersectingPair.getFirst().intersect(intersectingPair.getSecond());
			assert !(intersection instanceof EmptyDawgLetter<?, ?>);
			worklist.add(intersection);
			
			final Set<IDawgLetter<LETTER, COLNAMES>> difference1 = 
					intersectingPair.getFirst().difference(intersectingPair.getSecond());
			worklist.addAll(difference1);

			final Set<IDawgLetter<LETTER, COLNAMES>> difference2 = 
					intersectingPair.getSecond().difference(intersectingPair.getFirst());
			worklist.addAll(difference2);

			/*
			 * update the result map
			 */
			Set<IDawgLetter<LETTER, COLNAMES>> firstPreImage = result.getPreImage(intersectingPair.getFirst());
			Set<IDawgLetter<LETTER, COLNAMES>> secondPreImage = result.getPreImage(intersectingPair.getSecond());
			
			for (IDawgLetter<LETTER, COLNAMES> originalLetter : firstPreImage) {
				result.removePair(originalLetter, intersectingPair.getFirst());
				result.addPair(originalLetter, intersection);
				for (IDawgLetter<LETTER, COLNAMES> dl : difference1) {
					assert dl != null;
					assert !(dl instanceof EmptyDawgLetter<?, ?>) : "TODO: treat this case";
					result.addPair(originalLetter, dl);
				}
			}
			for (IDawgLetter<LETTER, COLNAMES> originalLetter : secondPreImage) {
				result.removePair(originalLetter, intersectingPair.getSecond());
				result.addPair(originalLetter, intersection);
				for (IDawgLetter<LETTER, COLNAMES> dl : difference2) {
					assert dl != null;
					assert !(dl instanceof EmptyDawgLetter<?, ?>) : "TODO: treat this case";
					result.addPair(originalLetter, dl);
				}
			}
		}

		return result;
	}

	/**
	 * Looks in the given set of letters for a pair of letters that is non-identical and has a non-empty
	 * intersection.
	 * Returns the first such pair it finds. Returns null iff there is no such pair.
	 * 
	 * @param letters
	 * @return
	 */
	private static <LETTER, COLNAMES> Pair<IDawgLetter<LETTER, COLNAMES>, IDawgLetter<LETTER, COLNAMES>> findIntersectingPair(
			DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory, 
			Set<IDawgLetter<LETTER, COLNAMES>> letters) {
		for (IDawgLetter<LETTER, COLNAMES> l1 : letters) {
			for (IDawgLetter<LETTER, COLNAMES> l2 : letters) {
				if (l1.equals(l2)) {
					continue;
				}
				if (l1.intersect(l2) instanceof EmptyDawgLetter<?, ?>) {
					continue;
				}
				return new Pair<IDawgLetter<LETTER,COLNAMES>, IDawgLetter<LETTER,COLNAMES>>(l1, l2);
			}
		}
		return null;
	}

	public static <LETTER, COLNAMES> boolean dawgLettersHaveSameSort(Set<IDawgLetter<LETTER, COLNAMES>> dawgLetters) {
		Object firstOccurringSort = null;
		for (IDawgLetter<LETTER, COLNAMES> dl : dawgLetters) {
			AbstractDawgLetter<LETTER, COLNAMES> adl = (AbstractDawgLetter<LETTER, COLNAMES>) dl;
			if (firstOccurringSort == null) {
				firstOccurringSort = adl.getSortId();
			}
			if (!firstOccurringSort.equals(adl.getSortId())) {
				return false;
			}
		}
		return true;
	}

	/**
	 * right now we only have different sorts when our colnames are of type TermVariable,
	 * otherwise we just have one dummy-String as Sort-Identifier.
	 */
	public static <COLNAMES> Object extractSortFromColname(COLNAMES cn) {
		if (TermVariable.class.isInstance(cn)) {
			TermVariable at = (TermVariable) cn;
			return at.getSort();
		}
//		assert false : "what to do here? (should only happen in unit-tests, right?)";
		return getDummySortId();
	}


	public static Object getDummySortId() {
		return "dummySort";
	}
	
	
	public static <COLNAMES> Set<COLNAMES> computeUnionSet(Set<COLNAMES> set1, Set<COLNAMES> set2) {
		final Set<COLNAMES> result = new HashSet<COLNAMES>();
		result.addAll(set1);
		result.addAll(set2);
		return result;
	}

	public static <COLNAMES> boolean isIntersectionEmpty(Set<COLNAMES> set1, Set<COLNAMES> set2) {
		final Set<COLNAMES> result = new HashSet<COLNAMES>();
		result.addAll(set1);
		result.retainAll(set2);
		return result.isEmpty();
	}

}
