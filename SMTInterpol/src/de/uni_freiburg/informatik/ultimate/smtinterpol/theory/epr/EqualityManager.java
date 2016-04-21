package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;

public class EqualityManager {
	
	HashMap<ApplicationTerm, HashSet<ApplicationTerm>> eqGraph = new HashMap<>();

	public void addEquality(ApplicationTerm a, ApplicationTerm b) {
		HashSet<ApplicationTerm> aTargets = eqGraph.get(a);
		if (aTargets == null)
			aTargets = new HashSet<>();
		aTargets.add(b);

		HashSet<ApplicationTerm> bTargets = eqGraph.get(b);
		if (bTargets == null)
			bTargets = new HashSet<>();
		bTargets.add(a);
	}

	public void backtrackEquality(ApplicationTerm a, ApplicationTerm b) {
		eqGraph.get(a).remove(b);
		eqGraph.get(b).remove(a);
	}
	
	public boolean isEqual(ApplicationTerm a, ApplicationTerm b) {
		ArrayDeque<ApplicationTerm> queue = new ArrayDeque<>();
		HashSet<ApplicationTerm> visited = new HashSet<>();
		
		queue.addLast(a);
		
		while (!queue.isEmpty()) {
			ApplicationTerm current = queue.pollFirst();
			
			if (current.equals(b)) 
				return true;
			
			visited.add(current);
			
			for (ApplicationTerm n : eqGraph.get(current)) {
				if (!visited.contains(n))
					queue.add(n);
			}
		}
		return false;
	}
}
