package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgbuilders;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

public class DawgBuilder<LETTER> {
	protected <K> void addLetterToMap(final Map<K, DawgLetter<LETTER>> map, final K key,
			final DawgLetter<LETTER> letter) {
		final DawgLetter<LETTER> old = map.get(key);
		map.put(key, old == null ? letter : old.union(letter));
	}

	protected Map<Set<DawgState<LETTER, Boolean>>, DawgLetter<LETTER>> merge(
			final Map<Set<DawgState<LETTER, Boolean>>, DawgLetter<LETTER>> oldMap,
			final DawgState<LETTER, Boolean> nextState, final DawgLetter<LETTER> nextLetter) {
		final Map<Set<DawgState<LETTER, Boolean>>, DawgLetter<LETTER>> newMap = new HashMap<>();
		final DawgLetter<LETTER> nextLetterComplement = nextLetter.complement();
		for (final Map.Entry<Set<DawgState<LETTER, Boolean>>, DawgLetter<LETTER>> entry : oldMap.entrySet()) {
			final DawgLetter<LETTER> letter = entry.getValue();
			if (!letter.isDisjoint(nextLetter)) {
				final DawgLetter<LETTER> intersect = letter.intersect(nextLetter);
				final Set<DawgState<LETTER, Boolean>> newSet = new HashSet<>();
				newSet.addAll(entry.getKey());
				newSet.add(nextState);
				addLetterToMap(newMap, newSet, intersect);
			}
			if (!letter.isDisjoint(nextLetterComplement)) {
				final DawgLetter<LETTER> intersect = letter.intersect(nextLetterComplement);
				final Set<DawgState<LETTER, Boolean>> newSet = entry.getKey();
				addLetterToMap(newMap, newSet, intersect);
			}
		}
		return newMap;
	}

}
