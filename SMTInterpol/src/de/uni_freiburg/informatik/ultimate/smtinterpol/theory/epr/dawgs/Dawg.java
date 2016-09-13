package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawgLetter.UniversalDawgLetter;

public class Dawg<LETTER, COLNAMES> extends AbstractDawg<LETTER, COLNAMES> {
	
	/*
	 * convention:
	 * states are just integers
	 * 
	 * the initial state is "0"
	 * the accepting state is <mArity>
	 * the sink state is "-1"
	 */
	
	/**
	 * Transition relation of the finite automaton as a nested map.
	 *  --> there are more efficient solutions, probably TODO
	 */
	Map<Integer, Map<IDawgLetter<LETTER>, Integer>> transitionRelation;

	public Dawg(SortedSet<COLNAMES> termVariables, Set<LETTER> allConstants) {
		super(termVariables, allConstants);
		
		/*
		 * create as an empty dawg
		 */
		addTransition(0, UniversalDawgLetter.INSTANCE, -1);
	}

	private void addTransition(int i, IDawgLetter<LETTER> dawgLetter, int j) {
		Map<IDawgLetter<LETTER>, Integer> letterToTarget = transitionRelation.get(i);
		if (letterToTarget == null) {
			letterToTarget = new HashMap<IDawgLetter<LETTER>, Integer>();
			transitionRelation.put(i, letterToTarget);
		}
		letterToTarget.put(dawgLetter, j);
	}

	@Override
	public IDawg<LETTER, COLNAMES> join(IDawg other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IDawg intersect(IDawg fp) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IDawg complement() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IDawg union(IDawg other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean accepts(List<LETTER> word) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isEmpty() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isUniversal() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void add(List<LETTER> arguments) {
		// TODO Auto-generated method stub
	
	}

	@Override
	public void addAll(IDawg dawg) {
		// TODO Auto-generated method stub
	
	}

	@Override
	public void removeAll(IDawg fpOne) {
		// TODO Auto-generated method stub
	
	}

	@Override
	public boolean supSetEq(IDawg<ApplicationTerm, TermVariable> points) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void addAllWithSubsetSignature(IDawg<LETTER, COLNAMES> d1) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public IDawg<LETTER, COLNAMES> select(Map<COLNAMES, LETTER> selectMap) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void removeAllWithSubsetSignature(IDawg<LETTER, COLNAMES> clFulfilledPoints) {
		// TODO Auto-generated method stub
		
	}

	@Override
	protected Iterable<List<LETTER>> listPoints() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterator<List<LETTER>> iterator() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isSingleton() {
		// TODO Auto-generated method stub
		return false;
	}


}
