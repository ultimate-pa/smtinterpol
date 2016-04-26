package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;

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
		for (SubsPair tp : substitution.subs) {
			if (tp instanceof TPair)
				addSubs(tp.top, (TermVariable) tp.bot);
			else
				addEquality((EqPair) tp);
		}
	}
	
	public ArrayList<CCEquality> getEqPathForEquality(ApplicationTerm a, ApplicationTerm b) {
		for (SubsPair sp : subs) {
			if (sp instanceof EqPair) {
				EqPair ep = (EqPair) sp;
				if ((ep.bot.equals(a) && ep.top.equals(b))
						|| (ep.bot.equals(b) && ep.top.equals(a))) {
					return ep.eqPath;
				}
			}
		}
		assert false : "should not happen..";
		return null;
	}
	
	public void addEquality(EqPair eqp) {
		addEquality(eqp.top, eqp.bot, eqp.eqPath);
	}

	/**
	 * @param top 
	 * @param bot
	 * @param eqPath a list of CCEqualities which are all true and together imply (= top bot)
	 */
	public void addEquality(Term top, Term bot, ArrayList<CCEquality> eqPath) {
		subs.add(new EqPair(top, bot, eqPath));
	}
	
	public void addSubs(Term top, TermVariable bot) {
		tvSet.add((TermVariable) bot);
		subs.add(new TPair(top, (TermVariable) bot));
	}
	
	public TermTuple apply(TermTuple tt) {
		if (subs.isEmpty())
			return tt;

		Term[] newTerms = Arrays.copyOf(tt.terms, tt.terms.length);//new Term[tt.terms.length];
		for (int i = 0; i < tt.terms.length; i++) {
			for (int j = 0; j < subs.size(); j++) {
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
	
	abstract class SubsPair {
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

	class EqPair extends SubsPair {

		ArrayList<CCEquality> eqPath;

		public EqPair(Term top, Term bot, ArrayList<CCEquality> eqPath) {
			super(top, bot);
			this.eqPath = eqPath;
		}
		
		@Override
		public String toString() {
			return String.format("(%s,%s)", top.toString(), bot.toString());

		}

	}

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
