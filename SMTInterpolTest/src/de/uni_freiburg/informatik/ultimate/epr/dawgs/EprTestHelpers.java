package de.uni_freiburg.informatik.ultimate.epr.dawgs;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;

public class EprTestHelpers {

	public static <LETTER, COLNAMES> void addConstantsWDefaultSort(
			DawgFactory<LETTER, COLNAMES> dawgFactoryStringString, Collection<LETTER> constants) {
		
		for (LETTER constant : constants) {
			dawgFactoryStringString.addConstant(EprHelpers.getDummySortId(), constant);
		}
	}

	static Collection<String> constantsAbc() {
		Set<String> constants = new HashSet<String>();
		constants.add("a");
		constants.add("b");
		constants.add("c");	
		return constants;
	}
	
	static Collection<String> constantsAbcde() {
		Set<String> constants = new HashSet<String>();
		constants.add("a");
		constants.add("b");
		constants.add("c");	
		constants.add("d");	
		constants.add("e");	
		return constants;
	}
}
