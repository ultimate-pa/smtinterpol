package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TTSubstitution {
//	ArrayList<TPair> subs;
	ArrayList<SubsPair> subs;
	HashSet<TermVariable> tvSet = new HashSet<>();

	
	public TTSubstitution() {
		super();
		this.subs = new ArrayList<>();
	}
	
	public TTSubstitution(TermVariable tv, Term t) {
		this();
		this.addSubs(t, tv);
	}
	
	public TTSubstitution(TTSubstitution substitution) {
		// TODO is DeepCopy necessary?
		this();
		for (SubsPair tp : substitution.subs)
			addSubs(tp.top, tp.bot);
	}
	
//	public void addSubs(TermVariable tv, Term t) {
	public void addSubs(Term top, Term bot) {
		if (bot instanceof TermVariable) {
			tvSet.add((TermVariable) bot);
			subs.add(new TPair(top, (TermVariable) bot));
		} else {
			subs.add(new SubsPair(top, bot));
		}
	}
	
	public TermTuple apply(TermTuple tt) {
		if (subs.isEmpty())
			return tt;

		Term[] newTerms = Arrays.copyOf(tt.terms, tt.terms.length);//new Term[tt.terms.length];
		for (int i = 0; i < tt.terms.length; i++) {
			for (int j = 0; j < subs.size(); j++) {
//				TPair tp = subs.get(j);
				SubsPair tp = subs.get(j);

				if (newTerms[i].equals(tp.bot))
					newTerms[i] = tp.top;
			}
		}
		return new TermTuple(newTerms);
	}
	
	/**
	 * true if application of this substitution is the identity function
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
	
	class SubsPair {
		Term top;
		Term bot;
		public SubsPair(Term top, Term bot) {
			this.top = top;
			this.bot = bot;
		}

		@Override
		public String toString() {
			return String.format("(%s,%s)", top.toString(), bot.toString());
		}
	}

//	class EqPair extends SubsPair {
//		Term t1;
//		Term t2;
//
//		public EqPair(Term top, Term bot) {
//			this.t1 = top;
//			this.t2 = bot;
//		}
//		
//		@Override
//		public String toString() {
//			return String.format("(%s,%s)", t1.toString(), t2.toString());
//		}
//
//	}

	class TPair extends SubsPair {
		Term t;
		TermVariable tv;

		public TPair(Term top, TermVariable bot) {
			super(top, bot);
			this.t = top;
			this.tv = bot;
		}
		
		@Override
		public String toString() {
			return String.format("(%s,%s)", tv.toString(), t.toString());
		}
	}
}
