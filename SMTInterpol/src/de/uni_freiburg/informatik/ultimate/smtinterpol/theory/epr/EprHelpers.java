package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.Stack;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackQuantifiedLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.EprPushState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;

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
			if (!(t instanceof ApplicationTerm))
				continue;
			for (Term p : ((ApplicationTerm) t).getParameters())
				if (p instanceof ApplicationTerm)
					result.add((ApplicationTerm) p);
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
			ApplicationTerm newTerm = theory.term(eqpa.getEprPredicate().getFunctionSymbol(), newTT.terms);
//			if (newTerm.getFreeVars().length > 0) {
//				resultAtom = eqpa.getEprPredicate().getAtomForQuantifiedTermTuple(newTT, theory, l.getAtom().getAssertionStackLevel());
//			} else {
//				resultAtom = eqpa.getEprPredicate().getAtomForPoint(newTT, theory, l.getAtom().getAssertionStackLevel());
//			}
			resultAtom = eqpa.getEprPredicate().getAtomForTermTuple(newTT, theory, l.getAtom().getAssertionStackLevel());
//			resultLit =  isPositive ? resultAtom : resultAtom.negate();
		} else if (atom instanceof EprQuantifiedEqualityAtom) {
			EprQuantifiedEqualityAtom eea = (EprQuantifiedEqualityAtom) atom;
			TermTuple newTT = sub.apply(eea.getArgumentsAsTermTuple());
			ApplicationTerm newTerm = theory.term("=", newTT.terms);
//			DPLLAtom resultAtom = null;
			if (newTerm.getFreeVars().length > 0) {
				resultAtom = new EprQuantifiedEqualityAtom(newTerm, 0, l.getAtom().getAssertionStackLevel());//TODO: hash
//			} else if (newTerm.getParameters()[0].equals(newTerm.getParameters()[1])) {
			} else {
				// TODO: will need a management for these atoms -- so there are no duplicates..
				//   it's not clear if we want CCEqualities or so, here..
//				return new EprGroundEqualityAtom(newTerm, 0, 0);
				resultAtom =  new EprGroundEqualityAtom(newTerm, 0, 0);
			}
			
			
//			return isPositive ? resultAtom : resultAtom.negate();
		} else {
			//assert false : "there might be equality replacements"; --> seems idiotic now..
			// literal is ground, just return it
			return l;
		}
		
		
		if (eprTheory.isGroundAllMode()) {
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
	
	public static class Pair<T,U> {
		public final T first;
		public final U second;
		
		public Pair(T f, U s) {
			first = f;
			second = s;
		}
	}

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
	public static <LETTER> Set<List<LETTER>> computeNCrossproduct(Set<LETTER> baseSet, int n) {
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
	
	public class EprClauseIterable implements Iterable<EprClause> {

		Iterator<EprPushState> mPushStateStack;

		public EprClauseIterable(Stack<EprPushState> pushStateStack) {
			mPushStateStack = pushStateStack.iterator();
		}

		@Override
		public Iterator<EprClause> iterator() {
			return new EprClauseIterator();
		}

		class EprClauseIterator implements Iterator<EprClause> {
			EprClause mNext;
			Iterator<EprClause> mCurrentPushStateClauseIterator;

			EprClauseIterator() {
				mNext = findNextEprClause();
			}

			public EprClause findNextEprClause() {
				if (! mPushStateStack.hasNext()) {
					return null;
				}
				mCurrentPushStateClauseIterator = mPushStateStack.next().getClausesIterator();

				// look for the first push state that has a clause
				while (! mCurrentPushStateClauseIterator.hasNext()) {
					if (!mPushStateStack.hasNext()) {
						return null;
					}
					mCurrentPushStateClauseIterator = mPushStateStack.next().getClausesIterator();
				}
				return mCurrentPushStateClauseIterator.next();
			}

			@Override
			public boolean hasNext() {
				return mNext != null;
			}

			@Override
			public EprClause next() {
				mNext = findNextEprClause();
				return mNext;
			}
		}
	}
	
	public class DecideStackLiteralIterable implements Iterable<DecideStackQuantifiedLiteral> {

		Iterator<EprPushState> mPushStateStack;

		public DecideStackLiteralIterable(Stack<EprPushState> pushStateStack) {
			mPushStateStack = pushStateStack.iterator();
		}

		@Override
		public Iterator<DecideStackQuantifiedLiteral> iterator() {
			return new DSLIterator();
		}

		class DSLIterator implements Iterator<DecideStackQuantifiedLiteral> {
			DecideStackQuantifiedLiteral mNext;
			Iterator<DecideStackQuantifiedLiteral> mCurrentPushStateClauseIterator;

			DSLIterator() {
				mNext = findNextEprClause();
			}

			public DecideStackQuantifiedLiteral findNextEprClause() {
				if (! mPushStateStack.hasNext()) {
					return null;
				}
				mCurrentPushStateClauseIterator = mPushStateStack.next().getDecideStackLiteralIterator();

				// look for the first push state that has a clause
				while (! mCurrentPushStateClauseIterator.hasNext()) {
					if (!mPushStateStack.hasNext()) {
						return null;
					}
					mCurrentPushStateClauseIterator = mPushStateStack.next().getDecideStackLiteralIterator();
				}
				return mCurrentPushStateClauseIterator.next();
			}

			@Override
			public boolean hasNext() {
				return mNext != null;
			}

			@Override
			public DecideStackQuantifiedLiteral next() {
				mNext = findNextEprClause();
				return mNext;
			}
		}
	}

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

	public static boolean haveSameSignature(IDawg... dawgs) {
		for (IDawg<ApplicationTerm, TermVariable> d1 : dawgs) {
			for (IDawg<ApplicationTerm, TermVariable> d2 : dawgs) {
				if (! d1.getColnames().equals(d2.getColnames())) {
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
			}

			return o1.toString().compareTo(o2.toString());//might work for all..
		}
		
	}

	public static <COLNAMES> Map<COLNAMES, Integer> computeColnamesToIndex(SortedSet<COLNAMES> sortedSet) {
		Map<COLNAMES, Integer> result = new HashMap<COLNAMES, Integer>();
		
		Iterator<COLNAMES> sortedSetIt = sortedSet.iterator();
		for (int i = 0; i < sortedSet.size(); i++) {
			result.put(sortedSetIt.next(), i);
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
					if (con.getSort().equals(tv.getSort())) {
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
					if (con.getSort().equals(tv.getSort())) {
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
//	public static <COLNAMES> SortedSet<COLNAMES> applyMapping(
//			SortedSet<COLNAMES> colnames, Map<COLNAMES, COLNAMES> translation) {
//		assert colnames.size > 0;
//		SortedSet<COLNAMES> result = new SortedSet<COLNAMES>(colnames));
//		for (
//			COLNAMES newEntry = translation.get(colnames[i]);
//			if (newEntry != null) {
//				result[i] = newEntry;
//			}
//		}
//		return result;
//	}
	
//	public static <LETTER, COLNAMES> List<LETTER> convertPointToNewSignature(
//			List<LETTER> point, Collection<COLNAMES> pointSignature, Collection<COLNAMES> newSignature) {
//		List<LETTER> result = new ArrayList<LETTER>(newSignature.size());
//		
//		return result;
//	}
}
