package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TTSubstitution {
	ArrayList<TPair> subs;
	HashSet<TermVariable> tvSet = new HashSet<>();

	
	public TTSubstitution() {
		super();
		this.subs = new ArrayList<>();
	}
	
	public TTSubstitution(TTSubstitution substitution) {
		// TODO is DeepCopy necessary?
		this.subs = new ArrayList<>();
		for (TPair tp : substitution.subs)
			addSubs(tp.tv, tp.t);
	}

	public void addSubs(TermVariable tv, Term t) {
		tvSet.add(tv);
		subs.add(new TPair(t, tv));
	}
	
	public TermTuple apply(TermTuple tt) {
		if (subs.isEmpty())
			return tt;

		Term[] newTerms = Arrays.copyOf(tt.terms, tt.terms.length);//new Term[tt.terms.length];
		for (int i = 0; i < tt.terms.length; i++) {
			for (int j = 0; j < subs.size(); j++) {
				TPair tp = subs.get(j);
//			for (TPair tp : subs) {
//				if (tt.terms[i].equals(tp.tv))
				if (newTerms[i].equals(tp.tv))
					newTerms[i] = tp.t;
//				else
////					newTerms[i] = tt.terms[i];
//					newTerms[i] = newTerms[i];
			}
		}
		return new TermTuple(newTerms);
	}
	
	/**
	 * true if application of this subtitution is the identity function
	 */
	public boolean isEmpty() {
		return subs.isEmpty();
	}
	
	public Set<TermVariable> tvSet() {
		return tvSet;
	}

	@Override
	public String toString() {
		return subs.toString();
	}

	class TPair {
		Term t;
		TermVariable tv;

		public TPair(Term top, TermVariable bot) {
			this.t = top;
			this.tv = bot;
		}
		
		@Override
		public String toString() {
			return String.format("(%s,%s)", tv.toString(), t.toString());
		}
	}
}
