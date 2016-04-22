package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;

public class EqualityManager {
	
	HashMap<ApplicationTerm, HashSet<ApplicationTerm>> eqGraph = new HashMap<>();
	HashMap<ApplicationTerm, HashMap<ApplicationTerm, CCEquality>> termPairToEquality = new HashMap<>();
	

	public void addEquality(ApplicationTerm a, ApplicationTerm b, CCEquality e) {
		updateTermPairToEquality(a, b, e);
		
		HashSet<ApplicationTerm> aTargets = eqGraph.get(a);
		if (aTargets == null) {
			aTargets = new HashSet<>();
			eqGraph.put(a, aTargets);
		}
		aTargets.add(b);

		HashSet<ApplicationTerm> bTargets = eqGraph.get(b);
		if (bTargets == null) {
			bTargets = new HashSet<>();
			eqGraph.put(b, bTargets);
		}
		bTargets.add(a);
	}

	private void updateTermPairToEquality(ApplicationTerm a, ApplicationTerm b, CCEquality e) {
		HashMap<ApplicationTerm, CCEquality> termToEquality = termPairToEquality.get(a);
		if (termToEquality == null) {
			termToEquality = new HashMap<>();
			termPairToEquality.put(a, termToEquality);
		}
		termToEquality.put(b, e);

		termToEquality = termPairToEquality.get(b);
		if (termToEquality == null) {
			termToEquality = new HashMap<>();
			termPairToEquality.put(b, termToEquality);
		}
		termToEquality.put(a, e);
	}
	
//	public CCEquality getCCEquality(ApplicationTerm a, ApplicationTerm b) {
//		return termPairToEquality.get(a).get(b);
//	}

	public void backtrackEquality(ApplicationTerm a, ApplicationTerm b) {
		eqGraph.get(a).remove(b);
		eqGraph.get(b).remove(a);
	}
	
	public ArrayList<CCEquality> isEqualRec(ApplicationTerm a, ApplicationTerm b, 
			ArrayList<CCEquality> pathSoFar, HashSet<ApplicationTerm> visited) {
		if (a.equals(b))
			return pathSoFar;
		if (eqGraph.get(a) == null)
			return null;
		for (ApplicationTerm trg : eqGraph.get(a)) {
			if (!visited.contains(trg)) {
				visited.add(trg);
				ArrayList<CCEquality> newPath = new ArrayList<>(pathSoFar);
				newPath.add(termPairToEquality.get(a).get(trg));
				ArrayList<CCEquality> res = isEqualRec(trg, b, newPath, visited);
				if (res != null)
					return res;
			}
		}
		return null;
	}

	/**
	 * 
	 * @param a
	 * @param b
	 * @return null if a and b are not equal in the current state, a list of CCEqualities which are set and by transitivity witness a=b otherwise
	 */
	public ArrayList<CCEquality> isEqual(ApplicationTerm a, ApplicationTerm b) {
//		ArrayDeque<ApplicationTerm> queue = new ArrayDeque<>();
		HashSet<ApplicationTerm> visited = new HashSet<>();
		ArrayList<CCEquality> path = new ArrayList<>();
		
		return isEqualRec(a, b, path, visited);
		
//		queue.addLast(a);
//		
//		while (!queue.isEmpty()) {
//			ApplicationTerm current = queue.pollFirst();
//			
//			if (current.equals(b)) 
//				return result;
//			
//			visited.add(current);
//			
//			for (ApplicationTerm n : eqGraph.get(current)) {
//				if (!visited.contains(n))
//					queue.add(n);
//			}
//		}
//		return null;
	}

//	public Object getCCEqualities() {
//		if (termPairTo)
//		// TODO Auto-generated method stub
//		return null;
//	}
}
