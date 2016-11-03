package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgLetter.UniversalDawgLetter;

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
	Map<Integer, Map<DawgLetter<LETTER>, Integer>> transitionRelation;

	public Dawg(SortedSet<COLNAMES> termVariables, Set<LETTER> allConstants, LogProxy logger) {
		super(termVariables, allConstants, logger);
		
		/*
		 * create as an empty dawg
		 */
		addTransition(0, UniversalDawgLetter.INSTANCE, -1);
	}

	private void addTransition(int i, DawgLetter<LETTER> dawgLetter, int j) {
		Map<DawgLetter<LETTER>, Integer> letterToTarget = transitionRelation.get(i);
		if (letterToTarget == null) {
			letterToTarget = new HashMap<DawgLetter<LETTER>, Integer>();
			transitionRelation.put(i, letterToTarget);
		}
		letterToTarget.put(dawgLetter, j);
	}

	@Override
	public IDawg<LETTER, COLNAMES> intersect(IDawg<LETTER, COLNAMES> fp) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IDawg<LETTER, COLNAMES> complement() {
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
	public IDawg<LETTER, COLNAMES> select(Map<COLNAMES, LETTER> selectMap) {
		// TODO Auto-generated method stub
		return null;
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

	@Override
	public boolean supSetEq(IDawg<LETTER, COLNAMES> points) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public IDawg<LETTER, COLNAMES> translatePredSigToClauseSig(Map<COLNAMES, Object> translation,
			SortedSet<COLNAMES> targetSignature) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IDawg<LETTER, COLNAMES> translateClauseSigToPredSig(Map<COLNAMES, COLNAMES> translation,
			List<Object> argList, SortedSet<COLNAMES> newSignature) {
		// TODO Auto-generated method stub
		return null;
	}
}
