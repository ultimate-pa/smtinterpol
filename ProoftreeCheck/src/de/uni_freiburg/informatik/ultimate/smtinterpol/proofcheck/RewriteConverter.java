/*
 * Copyright (C) 2012-2013 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import java.io.IOException;
import java.math.BigInteger;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * This class is used to convert a rewrite proof node (@rewrite).
 * A rewrite is used for substitution.
 * 
 * @author Christian Schilling
 */
public class RewriteConverter extends AConverter {
	// map for the rules
	private final HashMap<String, IRule> mAnnot2Rule;
	// lemma appendable
	private final Appendable mLemmaAppendable;
	// prefix :orSimp placeholder variables use
	private static final String PATTERN_VAR_PREFIX = "p";
	// index number of the pattern lemmata
	private int mLemmaNumber;
	// last pattern proof (not written immediately for 
	private PatternProof mLastPatternProof;
	
	/**
	 * @param appendable appendable to write the proof to
	 * @param theory the theory
	 * @param converter term converter
	 * @param simplifier computation simplifier
	 * @param lemmaAppendable appendable for the lemmata
	 */
	public RewriteConverter(final Appendable appendable, final Theory theory,
			final TermConverter converter,
			final ComputationSimplifier simplifier,
			final Appendable lemmaAppendable) {
		super(appendable, theory, converter, simplifier);
		mLemmaAppendable = lemmaAppendable;
		mLemmaNumber = 0;
		mLastPatternProof = null;
		
		// fill rule map
		mAnnot2Rule = new HashMap<String, RewriteConverter.IRule>(
				(int)(50 / 0.75) + 1);
		fillMap();
	}
	
	// [start] rules //
	
	/**
	 * This method fills the rule map with the rules.
	 * For each rule a conversion object is added to a hash map, which handles
	 * the conversion individually.
	 * 
	 * Here the rules could be changed or new ones added if necessary.
	 */
	private void fillMap() {
		// expansion of associative/chainable core functions
		mAnnot2Rule.put(":expand",
				new ExpandRule());
		// expansion of user-defined functions
		mAnnot2Rule.put(":expandDef",
				new ExpandDefRule());
		// equality of Boolean terms with 'True' and 'False' is false
		mAnnot2Rule.put(":trueNotFalse",
				new TrueNotFalseRule());
		// equality of different constants is false
		mAnnot2Rule.put(":constDiff",
				new ConstDiffRule());
		// equality with true is a conjunction
		mAnnot2Rule.put(":eqTrue",
				new EqTrueRule());
		// equality with false is a disjunction of negated terms
		mAnnot2Rule.put(":eqFalse",
				new EqFalseRule());
		// equality of syntactically equal terms is true
		mAnnot2Rule.put(":eqSame",
				new EqSameRule());
		// elimination of duplicates in equality (needs symmetry)
		mAnnot2Rule.put(":eqSimp",
				new EqSimpRule());
		// n-ary equality is a negated disjunction of negated binary equalities
		mAnnot2Rule.put(":eqBinary",
				new SimpleRule("(intro rw_eqBinary, rule not_not [symmetric])\n"));
		// distinctness with more than 2 Boolean arguments is false
		mAnnot2Rule.put(":distinctBool",
				new DistinctBoolRule());
		// distinctness for syntactically equal terms is false
		mAnnot2Rule.put(":distinctSame",
				new SimpleRule("(intro rw_distinctSame_fin "
						+ "rw_distinctSame_step rw_distinctSame_fin_bin)\n"));
		// distinctness of a Boolean term and its negation is false
		mAnnot2Rule.put(":distinctNeg",
				new DistinctNegRule());
		// distinctness of a Boolean term and 'True' is the negated term
		mAnnot2Rule.put(":distinctTrue",
				new DistinctTrueRule());
		// distinctness of a Boolean term and 'False' is the term
		mAnnot2Rule.put(":distinctFalse",
				new DistinctFalseRule());
		// n-ary distinctness is a negated disjunction of binary equalities
		mAnnot2Rule.put(":distinctBinary",
				new DistinctBinaryRule());
		// double negation and negations of Boolean constants
		mAnnot2Rule.put(":notSimp",
				new NotSimpRule());
		// absorption rule of disjunction
		mAnnot2Rule.put(":orSimp",
				new OrSimpRule());
		// disjunction with 'True' or a Boolean term and its negation is true
		mAnnot2Rule.put(":orTaut",
				new OrTautRule());
		// ite with condition 'True' is the first case
		mAnnot2Rule.put(":iteTrue",
				new SimpleRule("(rule HOL.if_True)\n"));
		// ite with condition 'False' is the second case
		mAnnot2Rule.put(":iteFalse",
				new SimpleRule("(rule HOL.if_False)\n"));
		// ite with syntactically equal cases is the only case
		mAnnot2Rule.put(":iteSame",
				new SimpleRule("(rule HOL.if_cancel)\n"));
		// ite with case 1 'True' and case 2 'False' is the condition
		mAnnot2Rule.put(":iteBool1",
				new SimpleRule("(rule rw_iteBool1)\n"));
		// ite with case 1 'False' and case 2 'True' is the negated condition
		mAnnot2Rule.put(":iteBool2",
				new SimpleRule("(rule rw_iteBool2)\n"));
		// ite with case 1 'True' is a disjunction of the condition and case 2
		mAnnot2Rule.put(":iteBool3",
				new SimpleRule("(rule rw_iteBool3)\n"));
		/*
		 * ite with case 1 'False' is a negated disjunction of the condition
		 * and negated case 2
		 */
		mAnnot2Rule.put(":iteBool4",
				new SimpleRule("(rule rw_iteBool4)\n"));
		/*
		 * ite with case 2 'True' is a disjunction of the negated condition
		 * and case 1
		 */
		mAnnot2Rule.put(":iteBool5",
				new SimpleRule("(rule rw_iteBool5)\n"));
		/*
		 * ite with case 2 'False' is a negated disjunction of the negated
		 * condition and the negated case 1
		 */
		mAnnot2Rule.put(":iteBool6",
				new SimpleRule("(rule rw_iteBool6)\n"));
		// logical and rewrite to disjunction
		mAnnot2Rule.put(":andToOr",
				new SimpleRule("(intro rw_andToOr, rule HOL.not_not [symmetric])\n"));
		// xor rewrite to distinct
		mAnnot2Rule.put(":xorToDistinct",
				new SimpleRule("(rule rw_xorToDistinct)\n"));
		// implication rewrite to disjunction
		mAnnot2Rule.put(":impToOr",
				new ImpToOrRule());
		/*
		 * remove annotation
		 * (should neither be translated nor substituted, since annotations are
		 * automatically dropped)
		 */
		mAnnot2Rule.put(":strip",
				new SimpleRule(ProofConverter.G_ONLY_SUBSTITUTE));
		// canonical form of arithmetic terms: (+ (* a1 x1) ... (* an xn) an+1)
		mAnnot2Rule.put(":canonicalSum",
				new SimpleRule(mSimplifier.getRule() + "\n"));
		// binary '<=' to canonical form
		mAnnot2Rule.put(":leqToLeq0",
				new SimpleRule("(rule rw_leqToLeq0, " + mSimplifier.getRule()
						+ ")\n"));
		// binary '<' to canonical form
		mAnnot2Rule.put(":ltToLeq0",
				new SimpleRule("(rule rw_ltToLeq0, " + mSimplifier.getRule()
						+ ")\n"));
		// binary '>=' to canonical form
		mAnnot2Rule.put(":geqToLeq0",
				new SimpleRule("(rule rw_geqToLeq0, " + mSimplifier.getRule()
						+ ")\n"));
		// binary '>' to canonical form
		mAnnot2Rule.put(":gtToLeq0",
				new SimpleRule("(rule rw_gtToLeq0, " + mSimplifier.getRule()
						+ ")\n"));
		// constant comparison with zero
		mAnnot2Rule.put(":leqTrue",
				new SimpleRule(mSimplifier.getRule() + "\n"));
		// constant comparison with zero
		mAnnot2Rule.put(":leqFalse",
				new SimpleRule(mSimplifier.getRule() + "\n"));
		// correct typing in mixed logic
		mAnnot2Rule.put(":desugar",
				new SimpleRule(mSimplifier.getRule() + "\n"));
		// divisible rewrite
		mAnnot2Rule.put(":divisible",
				new DivisibleRule());
		// modulo with constant second term different from 0
		mAnnot2Rule.put(":modulo",
				new SimpleRule("(rule rw_modulo, " + mSimplifier.getRule()
						+ ")\n"));
		// modulo by 1 is 0
		mAnnot2Rule.put(":modulo1",
				new SimpleRule("(rule rw_modulo1)\n"));
		// modulo by -1 is 0
		mAnnot2Rule.put(":modulo-1",
				new SimpleRule("(rule rw_moduloM1)\n"));
		// constant modulo result
		mAnnot2Rule.put(":moduloConst",
				new SimpleRule("(unfold SMTmod_def, " + mSimplifier.getRule()
						+ ")\n"));
		// division by 1 does not change
		mAnnot2Rule.put(":div1",
				new SimpleRule("(rule rw_div1)\n"));
		// division by -1 only inverts
		mAnnot2Rule.put(":div-1",
				new DivM1Rule());
		// constant division result
		mAnnot2Rule.put(":divConst",
				new SimpleRule("(unfold SMTdiv_def, " + mSimplifier.getRule()
						+ ")\n"));
		// integer conversion of a constant
		mAnnot2Rule.put(":toInt",
				new SimpleRule("(subst Orderings.order_class.eq_iff, "
						+ mSimplifier.getRule() + ")\n"));
		// real conversion of constants
		mAnnot2Rule.put(":toReal",
				new SimpleRule("(simp only: THF_Arith.int_to_real_def)\n"));
		// flattening of disjunctions
		mAnnot2Rule.put(":flatten",
				new SimpleRule("(intro HOL.refl rw_flatten_drop rw_flatten_par)\n"));
	}
	
	/**
	 * This interface is used for the rule translation.
	 */
	private interface IRule {
		/**
		 * @param equality the tautology
		 * @return the proof rule (keywords for special cases!)
		 */
		String convert(final ApplicationTerm equality);
	}
	
	/**
	 * This class translates trivial rules that need no further investigation.
	 */
	private class SimpleRule implements IRule {
		// Isabelle rule
		private final String mRule;
		
		/**
		 * @param rule the rule
		 */
		public SimpleRule(final String rule) {
			mRule = rule;
		}
		
		/**
		 * The rule is simply written without any additional steps.
		 * 
		 * {@inheritDoc}
		 */
		@Override
		public String convert(final ApplicationTerm equality) {
			return mRule;
		}
	}
	
	/**
	 * This class converts the :expand rule.
	 * 
	 * The translation already prints most of the interpreted functions in the
	 * correct expansion, so the rule can be ignored.
	 * 
	 * The interpreted functions it is used for are:
	 *   xor, +, -, *, /, div, <, >, <=, >=
	 * The latter four functions add conjunctions with associativity different
	 * from Isabelle, so this has to be translated.
	 * 
	 * These other functions have their own treatment rewrites:
	 *   and, =>, =, distinct
	 */
	private class ExpandRule implements IRule {
		@Override
		public String convert(ApplicationTerm equality) {
			assert (equality.getParameters()[0] instanceof ApplicationTerm);
			final ApplicationTerm lhs =
					(ApplicationTerm)equality.getParameters()[0];
			final String function = lhs.getFunction().getName();
			
			/*
			 * the comparison predicates have to be handled separately,
			 * but only for more than three arguments
			 */
			if ((lhs.getParameters().length > 3)
					&& ((function == "<") || (function == "<=")
					|| (function == ">") || (function == ">="))) {
				return "(intro rw_expand, rule HOL.refl)\n";
			} else {
				// these cases are already correclty translated
				return ProofConverter.G_ONLY_SUBSTITUTE;
			}
		}
	}
	
	/**
	 * This class converts the :expandDef rule.
	 * 
	 * It just unfolds the definition and finishes by reflexivity.
	 */
	private class ExpandDefRule implements IRule {
		@Override
		public String convert(ApplicationTerm equality) {
			assert (equality.getParameters()[0] instanceof ApplicationTerm);
			
			final StringBuilder builder = new StringBuilder(32);
			builder.append("(unfold ");
			builder.append(mConverter.getFunctionName(
					((ApplicationTerm)equality.getParameters()[0]).
							getFunction()));
			builder.append("_def, rule refl)\n");
			return builder.toString();
		}
	}
	
	/**
	 * This class converts the :trueNotFalse rule.
	 * 
	 * The proof in Isabelle depends on whether 'True' or 'False' comes first.
	 * The term is then propagated to the right until the other term is found,
	 * which finishes the proof.
	 * There are sixteen possible cases.
	 */
	private class TrueNotFalseRule implements IRule {
		@Override
		public String convert(final ApplicationTerm equality) {
			assert ((equality.getParameters()[0] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getFunction().getName() == "=")
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getParameters().length > 1));
			final Term[] eqTerms =
					((ApplicationTerm)equality.getParameters()[0]).
							getParameters();
			
			/*
			 * Find the first occurrence of 'True' or 'False'.
			 */
			final ApplicationTerm otherTerm;
			
			int i = 0;
			while (true) {
				assert (i < eqTerms.length - 1) : "The first Boolean constant must be found.";
				final Term term = eqTerms[i];
				
				// first found 'True'
				if (term == mTheory.mTrue) {
					otherTerm = mTheory.mFalse;
					break;
				} else if (term == mTheory.mFalse) {
					// first found 'False'
					otherTerm = mTheory.mTrue;
					break;
				}
				++i;
			}
			
			int j = i + 1;
			while (j < eqTerms.length) {
				if (eqTerms[j] == otherTerm) {
					break;
				}
				++j;
			}
			assert (j < eqTerms.length) : "The other Boolean constant must be found.";
			
			// write proof
			final StringBuilder builder = new StringBuilder(32);
			builder.append("(intro ");
			final String type = (otherTerm == mTheory.mFalse) ? "T" : "F";
			
			// constants are neighbors
			if (j == i + 1) {
				builder.append("rw_tnf_nb");
				builder.append(type);
				
				// constants are the last two terms
				if (j == eqTerms.length - 1) {
					builder.append("_last");
				}
			} else {
				// propagation between constants needed
				// second constant is the last term
				if (j == eqTerms.length - 1) {
					builder.append("rw_tnf_prop");
					builder.append(type);
					builder.append("_last rw_tnf_prop");
					builder.append(type);
				} else {
					builder.append("rw_tnf_nb");
					builder.append(type);
					builder.append(" rw_tnf_prop");
					builder.append(type);
				}
			}
			
			// no elimination of previous equalities needed
			if (i == 0) {
				builder.append(")\n");
			} else {
				// elimination of previous equalities needed
				builder.append(" rw_tnf_elim)\n");
			}
			
			return builder.toString();
		}
	}
	
	/**
	 * This class converts the :constDiff rule.
	 * 
	 * For binary equalities the proof is trivial. Else the first two distinct
	 * constant terms are found. In the proof the first constant is propagated
	 * to the right until the other term is found, which finishes the proof.
	 */
	private class ConstDiffRule implements IRule {
		@Override
		public String convert(final ApplicationTerm equality) {
			assert ((equality.getParameters()[0] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getFunction().getName() == "="));
			final Term[] terms = ((ApplicationTerm)equality.
					getParameters()[0]).getParameters();
			assert (terms.length > 1);
			
			if (terms.length == 2) {
				return "(rule rw_constDiff_bin, " + mSimplifier.getRule() + ")\n";
			} else {
				// find the distinct constants
				final ConstantTerm c, d;
				int i = 0;
				while (true) {
					if (terms[i] instanceof ConstantTerm) {
						c = (ConstantTerm)terms[i];
						break;
					}
					++i;
					assert (i < terms.length);
				}
				int j = i + 1;
				while (true) {
					if (terms[j] instanceof ConstantTerm) {
						final ConstantTerm ct = (ConstantTerm)terms[j];
						if (c != ct) {
							d = ct;
							break;
						}
					}
					++j;
					assert (j < terms.length);
				}
				
				// write rule
				final StringBuilder builder = new StringBuilder();
				builder.append("(rule rw_constDiff_start [where c = \"");
				mConverter.convertToAppendable(c, builder);
				builder.append("\" and d = \"");
				mConverter.convertToAppendable(d, builder);
				builder.append("\"], ");
				builder.append(mSimplifier.getRule());
				builder.append(", elim");
				
				// at least one argument is given
				assert ((j < terms.length - 1) || (i < j - 1) || (i > 0));
				
				// stop when the second constant was found
				if (j < terms.length - 1) {
					builder.append(" rw_constDiff_fin");
				}
				
				// only step if there are terms in between
				if (i < j - 1) {
					builder.append(" rw_constDiff_step");
				}
				
				// ignore all equalities before the first constant
				if (i > 0) {
					builder.append(" rw_constDiff_elim)\n");
				} else {
					builder.append(")\n");
				}
				
				return builder.toString();
			}
		}
	}
	
	/**
	 * This class converts the :eqTrue rule.
	 * 
	 * It uses a pattern proof, since otherwise there would be too many cases
	 * to consider.
	 */
	private class EqTrueRule implements IRule {
		@Override
		public String convert(ApplicationTerm equality) {
			assert ((equality.getParameters()[0] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getFunction().getName() == "=")
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getParameters().length > 1));
			final Term[] lhs = ((ApplicationTerm)equality.getParameters()[0]).
					getParameters();
			final Term rhsTerm = equality.getParameters()[1];
			final Term[] rhs;
			if ((rhsTerm instanceof ApplicationTerm)
					&& (((ApplicationTerm)rhsTerm).getFunction()
					== mTheory.mAnd)) {
				rhs = ((ApplicationTerm)rhsTerm).getParameters();
			} else {
				rhs = new Term[1];
				rhs[0] = rhsTerm;
			}
			final ApplicationTerm truth = mTheory.mTrue;
			
			// binary case
			if (lhs.length == 2) {
				if (lhs[0] == truth) {
					assert (lhs[1] == equality.getParameters()[1]);
					return "(rule HOL.simp_thms(11))\n";
				} else {
					assert ((lhs[0] == equality.getParameters()[1])
							&& (lhs[1] == truth));
					return "(rule HOL.eq_True)\n";
				}
			}
			
			// n-ary case: proof by simplifier
			final StringBuilder proof = new StringBuilder(512);
			proof.append("\n(simp only: HOL.simp_thms(11) HOL.eq_True "
					+ "HOL.simp_thms(21) HOL.simp_thms(22)");
			
			// right-hand side is a disjunction
			if (rhs.length > 1) {
				proof.append(" rw_eqTrue_merge_left rw_eqTrue_merge_right "
					+ "rw_eqTrue_merge_left_bin rw_eqTrue_merge_right_bin");
			}
			
			// optional removing of duplicates
			proof.append(", (simp only: HOL.conj_absorb "
					+ "HOL.conj_left_absorb HOL.conj_commute "
					+ "HOL.conj_left_commute) ?)\n");
			
			final Term[] patternLeft = new Term[lhs.length];
			final Term[] patternRight = new Term[rhs.length];
			
			setUpEqPattern(lhs, patternLeft, rhs, patternRight, truth);
			
			final FunctionSymbol eq = equality.getFunction();
			
			return getMainProof(
					mTheory.term(eq,
							mTheory.term(eq, patternLeft),
							(patternRight.length == 1)
									? patternRight[0]
									: mTheory.term(mTheory.mAnd,
											patternRight)),
					proof.toString());
		}
	}
	
	/**
	 * This class converts the :eqFalse rule.
	 * 
	 * It uses a pattern proof, since otherwise there would be too many cases
	 * to consider.
	 */
	private class EqFalseRule implements IRule {
		@Override
		public String convert(ApplicationTerm equality) {
			assert ((equality.getParameters()[0] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getFunction().getName() == "=")
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getParameters().length > 1)
					&& (equality.getParameters()[1] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[1]).
							getFunction() == mTheory.mNot)
					&& (((ApplicationTerm)equality.getParameters()[1]).
							getParameters().length == 1));
			final Term[] lhs = ((ApplicationTerm)equality.getParameters()[0]).
					getParameters();
			final Term rhsTerm = ((ApplicationTerm)equality.
					getParameters()[1]).getParameters()[0];
			final Term[] rhs;
			if ((rhsTerm instanceof ApplicationTerm)
				&& (((ApplicationTerm)rhsTerm).getFunction() == mTheory.mOr)) {
				rhs = ((ApplicationTerm)rhsTerm).getParameters();
			} else {
				rhs = new Term[1];
				rhs[0] = rhsTerm;
			}
			final ApplicationTerm falsity = mTheory.mFalse;
			
			// binary case
			if (lhs.length == 2) {
				if (lhs[0] == falsity) {
					assert (mTheory.term(mTheory.mNot, lhs[1])
							== equality.getParameters()[1]);
					return "(rule HOL.simp_thms(13))\n";
				} else {
					assert ((mTheory.term(mTheory.mNot, lhs[0])
							== equality.getParameters()[1])
								&& (lhs[1] == falsity));
					return "(rule HOL.simp_thms(14))\n";
				}
			}
			
			// n-ary case: proof by simplifier
			final StringBuilder proof = new StringBuilder(512);
			proof.append("(simp only: HOL.refl HOL.simp_thms(13) "
					+ "HOL.simp_thms(14) HOL.simp_thms(21) HOL.simp_thms(22)");
			
			// right-hand side is a disjunction
			if (rhs.length > 1) {
				proof.append(" rw_eqFalse_merge_left rw_eqFalse_merge_right "
					+ "rw_eqFalse_merge_left_bin rw_eqFalse_merge_right_bin");
			}
			
			// optional removing of duplicates
			proof.append(", (simp only: HOL.conj_absorb "
					+ "HOL.conj_left_absorb HOL.conj_commute "
					+ "HOL.conj_left_commute) ?");
			
			// de Morgan's rule to solve the negated disjunction
			if (rhs.length > 1) {
				proof.append(", (intro rw_eqFalse_deMorgan HOL.refl)");
			}
			
			proof.append(")\n");
			
			final Term[] patternLeft = new Term[lhs.length];
			final Term[] patternRight = new Term[rhs.length];
			
			setUpEqPattern(lhs, patternLeft, rhs, patternRight, falsity);
			
			final FunctionSymbol eq = equality.getFunction();
			final FunctionSymbol not = mTheory.mNot;
			
			return getMainProof(
					mTheory.term(eq,
							mTheory.term(eq, patternLeft),
							(patternRight.length == 1)
									? mTheory.term(not, patternRight[0])
									: mTheory.term(not,
											mTheory.term(mTheory.mOr,
											patternRight))),
					proof.toString());
		}
	}
	
	/**
	 * This method creates the patterns for both the :eqTrue and the :eqFalse
	 * rule, since their structure only differs in the Boolean constant.
	 * 
	 * @param originLeft the original left equality terms
	 * @param patternLeft the pattern left equality terms
	 * @param originRight the original right equality terms
	 * @param patternRight the pattern right equality terms
	 * @param constant Boolean constant
	 */
	private void setUpEqPattern(final Term[] originLeft,
			final Term[] patternLeft, final Term[] originRight,
			final Term[] patternRight, final ApplicationTerm constant) {
		assert (originLeft.length == patternLeft.length);
		
		final HashMap<Term, Term> term2patVar = new HashMap<Term, Term>(
				(int)(patternRight.length / 0.75) + 1);
		
		/* create conjunction object */
		final Term[] params = new Term[0];
		final Sort[] paramSorts = new Sort[0];
		
		int index = 0;
		for (int i = 0; i < patternRight.length; ++i) {
			assert ((originRight[i] != constant)
					&& (term2patVar.get(originRight[i]) == null))
				: "Right-hand side should contain no duplicates or constant.";
			
			final Term patternVar = getTerm(PATTERN_VAR_PREFIX + ++index,
						params, paramSorts);
			term2patVar.put(originRight[i], patternVar);
			patternRight[i] = patternVar;
		}
		
		for (int i = 0; i < originLeft.length; ++i) {
			final Term equalityTerm = originLeft[i];
			if (equalityTerm == constant) {
				patternLeft[i] = constant;
			} else {
				assert (term2patVar.get(equalityTerm) != null);
				patternLeft[i] = term2patVar.get(equalityTerm);
			}
		}
	}
	
	/**
	 * This class converts the :eqSame rule.
	 * 
	 * The only difference in the translation is due to the length of the
	 * equality (two, three, or more terms).
	 */
	private class EqSameRule implements IRule {
		@Override
		public String convert(final ApplicationTerm equality) {
			assert ((equality.getParameters()[0] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getFunction().getName() == "=")
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getParameters().length > 1));
			final int arguments = ((ApplicationTerm)equality.
					getParameters()[0]).getParameters().length;
			
			// binary equality needs no absorption
			if (arguments == 2) {
				return "(rule HOL.simp_thms(6))\n";
			} else if (arguments == 3) {
				// equality with more than 2 terms needs only binary absorption
				return "(rule rw_eqSame_bin)\n";
			} else {
				// equality with more than 3 terms also needs non-binary absorption
				return "(intro rw_eqSame, rule rw_eqSame_bin)\n";
			}
		}
	}
	
	/**
	 * This class converts the :eqSimp rule.
	 * 
	 * It uses a pattern proof to prevent the simplifier from rewriting inside
	 * bigger terms.
	 */
	private class EqSimpRule implements IRule {
		@Override
		public String convert(ApplicationTerm equality) {
			assert ((equality.getParameters()[0] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getFunction().getName() == "=")
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getParameters().length > 1)
					&& (equality.getParameters()[1] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[1]).
							getFunction().getName() == "=")
					&& (((ApplicationTerm)equality.getParameters()[1]).
							getParameters().length > 1));
			final Term[] lhs = ((ApplicationTerm)equality.getParameters()[0]).
					getParameters();
			final Term[] rhs = ((ApplicationTerm)equality.getParameters()[1]).
					getParameters();
			assert (rhs.length > 1);
			final Term[] patternLeft = new Term[lhs.length];
			final Term[] patternRight = new Term[rhs.length];
			
			final HashMap<Term, Term> term2patVar = new HashMap<Term, Term>(
					(int)(rhs.length / 0.75) + 1);
			
			/* create conjunction object */
			final Term[] params = new Term[0];
			final Sort[] paramSorts = new Sort[0];
			
			int index = 0;
			for (int i = 0; i < rhs.length; ++i) {
				assert (term2patVar.get(rhs[i]) == null)
					: "Right-hand side should contain no duplicates.";
				final Term patternVar = getTerm(PATTERN_VAR_PREFIX + ++index,
							params, paramSorts);
				term2patVar.put(rhs[i], patternVar);
				patternRight[i] = patternVar;
			}
			
			for (int i = 0; i < lhs.length; ++i) {
				final Term equalityTerm = lhs[i];
				assert (term2patVar.get(equalityTerm) != null);
				patternLeft[i] = term2patVar.get(equalityTerm);
			}
			
			final FunctionSymbol eq = equality.getFunction();
			
			return getMainProof(mTheory.term(eq,
					mTheory.term(eq, patternLeft),
					mTheory.term(eq, patternRight)),
					"(simp only: HOL.conj_absorb HOL.conj_left_absorb "
					+ "HOL.conj_commute HOL.conj_left_commute HOL.eq_commute)\n"
			);
		}
	}
	
	/**
	 * This class converts the :distinctBool rule.
	 * 
	 * The only case distinction is in whether the distinctness has three or
	 * more arguments. Distinctness is shown for the first three terms.
	 */
	private class DistinctBoolRule implements IRule {
		@Override
		public String convert(final ApplicationTerm equality) {
			assert ((equality.getParameters()[0] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getFunction().getName() == "distinct")
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getParameters().length > 2));
			
			// ternary distinct uses a direct rule
			if (((ApplicationTerm)equality.getParameters()[0]).
			getParameters().length == 3) {
				return "(rule rw_distinctBool_ter)\n";
			} else {
				// all other cases show non-distinctness of the first three terms
				return "(rule rw_distinctBool_start, intro "
						+ "rw_distinctBool_fin rw_distinctBool_elim)\n";
			}
		}
	}
	
	/**
	 * This class converts the :distinctNeg rule.
	 * 
	 * The cases are whether 'True' and 'False' occur and whether the negated
	 * term is the first or the second one.
	 */
	private class DistinctNegRule implements IRule {
		@Override
		public String convert(final ApplicationTerm equality) {
			assert ((equality.getParameters()[0] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getFunction().getName() == "distinct")
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getParameters().length == 2));
			final Term[] distinct = ((ApplicationTerm)equality.getParameters()[0]).getParameters();
			final Term lhs = distinct[0];
			
			/* base cases: 'True' and 'False' */
			if (lhs == mTheory.mTrue) {
				assert (distinct[1] == mTheory.mFalse);
				return "(rule rw_distinctNeg_tf)\n";
			} else if (lhs == mTheory.mFalse) {
				assert (distinct[1] == mTheory.mTrue);
				return "(rule rw_distinctNeg_ft)\n";
			} else if ((lhs instanceof ApplicationTerm)
					&& (((ApplicationTerm)lhs).getFunction() == mTheory.mNot)
					&& (((ApplicationTerm)lhs).getParameters()[0] == distinct[1])) {
				/* arbitrary terms */
				return "(rule rw_distinctNeg_np)\n";
			} else {
				assert ((distinct[1] instanceof ApplicationTerm)
						&& ((ApplicationTerm)distinct[1]).getFunction()
								== mTheory.mNot)
						&& (((ApplicationTerm)distinct[1]).getParameters()[0]
								== lhs);
				return "(rule rw_distinctNeg_pn)\n";
			}
		}
	}
	
	/**
	 * This class converts the :distinctTrue rule.
	 * 
	 * The rule depends on whether 'True' is the first or the second term.
	 */
	private class DistinctTrueRule implements IRule {
		@Override
		public String convert(final ApplicationTerm equality) {
			assert ((equality.getParameters()[0] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getFunction().getName() == "distinct") 
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getParameters().length == 2));
			
			// 'True' is the first term
			if (((ApplicationTerm)equality.getParameters()[0]).
					getParameters()[0] == mTheory.mTrue) {
				return "(rule rw_distinctTrue_l)\n";
			} else {
				// 'True' is the second term
				assert (((ApplicationTerm)equality.getParameters()[0]).
						getParameters()[1] == mTheory.mTrue);
				return "(rule rw_distinctTrue_r)\n";
			}
		}
	}
	
	/**
	 * This class converts the :distinctFalse rule.
	 * 
	 * The rule depends on whether 'False' is the first or the second term.
	 */
	private class DistinctFalseRule implements IRule {
		@Override
		public String convert(final ApplicationTerm equality) {
			assert ((equality.getParameters()[0] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getFunction().getName() == "distinct")
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getParameters().length == 2));
			
			// 'False' is the first term
			if (((ApplicationTerm)equality.getParameters()[0]).
					getParameters()[0] == mTheory.mFalse) {
				return "(rule rw_distinctFalse_l)\n";
			} else {
				// 'False' is the second term
				assert (((ApplicationTerm)equality.getParameters()[0]).
						getParameters()[1] == mTheory.mFalse);
				return "(rule rw_distinctFalse_r)\n";
			}
		}
	}
	
	/**
	 * This class converts the :distinctBinary rule.
	 * 
	 * A binary non-Boolean distinct rewrite is ignored, since the translation
	 * already does the job. For binary Boolean rewrites the first term is
	 * negated again if already negated before, else the second term is
	 * negated.
	 * Distinct with more arguments uses the obvious translation.
	 */
	private class DistinctBinaryRule implements IRule {
		@Override
		public String convert(final ApplicationTerm equality) {
			assert ((equality.getParameters()[0] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getFunction().getName() == "distinct")
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getParameters().length > 1));
			
			// binary case
			if (((ApplicationTerm)equality.getParameters()[0]).
					getParameters().length == 2) {
				final Term first = ((ApplicationTerm)equality.
						getParameters()[0]).getParameters()[0];
				// Boolean case is handled differently
				if (first.getSort() == mTheory.getBooleanSort()) {
					if ((first instanceof ApplicationTerm)
						&& ((ApplicationTerm)first).getFunction()
								== mTheory.mNot) {
						return "(rule rw_distinctBinary_bin_first)\n";
					} else {
						return "(rule rw_distinctBinary_bin_second)\n";
					}
				} else {
					// all other cases are automatically correct by the translation
					return ProofConverter.G_ONLY_SUBSTITUTE;
				}
			} else {
				// apply variation of de Morgan's rule, finish with reflexivity
				return "(intro rw_distinctBinary_more, rule HOL.refl)\n";
			}
		}
	}
	
	/**
	 * This class converts the :notSimp rule.
	 * 
	 * The negations for Boolean constants are handled differently.
	 */
	private class NotSimpRule implements IRule {
		@Override
		public String convert(final ApplicationTerm equality) {
			final Term rhs = equality.getParameters()[1];
			// trivial negation of 'True'
			if (rhs == mTheory.mFalse) {
				return "(rule HOL.not_True_eq_False)\n";
			} else if (rhs == mTheory.mTrue) {
				// trivial negation of 'False'
				return "(rule HOL.not_False_eq_True)\n";
			} else {
				// double negation
				return "(rule HOL.not_not)\n";
			}
		}
	}
	
	/**
	 * This class converts the :orSimp rule.
	 * 
	 * It uses a pattern proof, since otherwise there would be too many cases
	 * to consider.
	 */
	private class OrSimpRule implements IRule {
		@Override
		public String convert(ApplicationTerm equality) {
			assert ((equality.getParameters()[0] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getFunction() == mTheory.mOr)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getParameters().length > 1));
			
			final Term[] lhs = ((ApplicationTerm)equality.
					getParameters()[0]).getParameters();
			final Term[] patternLeft = new Term[lhs.length];
			
			final Term rhs = equality.getParameters()[1];
			final Term[] patternRight;
			if ((rhs instanceof ApplicationTerm)
					&& (((ApplicationTerm)rhs).getFunction() == mTheory.mOr)) {
				patternRight = new Term[((ApplicationTerm)rhs).getParameters().
				                        length];
			} else {
				patternRight = new Term[1];
			}
			
			final HashMap<Term, Term> disjunct2patVar =
					new HashMap<Term, Term>(
							(int)(patternRight.length / 0.75) + 1);
			int index = 0;
			
			/* create disjunction object */
			final Term[] params = new Term[0];
			final Sort[] paramSorts = new Sort[0];
			final ApplicationTerm falsity = mTheory.mFalse;
			
			int j = -1;
			for (int i = 0; i < patternLeft.length; ++i) {
				final Term disjunct = lhs[i];
				if (disjunct == falsity) {
					patternLeft[i] = falsity;
				} else {
					Term patternVar = disjunct2patVar.get(disjunct);
					if (patternVar == null) {
						patternVar = getTerm(PATTERN_VAR_PREFIX + ++index, params,
								paramSorts);
						disjunct2patVar.put(disjunct, patternVar);
						patternRight[++j] = patternVar;
					}
					patternLeft[i] = patternVar;
				}
			}
			
			final String proof;
			
			// disjunction only contains 'False', so there is an easier proof
			if ((patternRight.length == 1) && (rhs == falsity)) {
				patternRight[0] = falsity;
				proof = "(simp only: HOL.simp_thms(32))\n";
			} else {
				// at least one disjunct is not 'False'
				proof = "(simp only: HOL.disj_commute "
						+ "HOL.disj_left_commute HOL.disj_absorb "
						+ "HOL.disj_left_absorb HOL.simp_thms(31) "
						+ "HOL.simp_thms(32))\n";
			}
			assert (patternRight[patternRight.length - 1] != null);
			
			final FunctionSymbol or = mTheory.mOr;
			
			return getMainProof(
					mTheory.term(equality.getFunction(),
							mTheory.term(or, patternLeft),
							(patternRight.length == 1)
									? patternRight[0]
									: mTheory.term(or, patternRight)),
					proof);
		}
	}
	
	/**
	 * This class converts the :orTaut rule.
	 * 
	 * It uses a pattern proof and discriminates between the reason ('True' vs.
	 * 'P | ~ P').
	 */
	private class OrTautRule implements IRule {
		private class TermNegationWrapper {
			// the term
			private final Term mTerm;
			// true iff term was negated
			private final boolean mIsNegated;
			
			/**
			 * @param term the term (without negation)
			 * @param isNegated true iff term was negated
			 */
			public TermNegationWrapper(Term term, boolean isNegated) {
				mTerm = term;
				mIsNegated = isNegated;
			}
			
			@Override
			public int hashCode() {
				return mTerm.hashCode();
			}
			
			@Override
			public boolean equals(Object o) {
				return mTerm.equals(o);
			}
			
			@Override
			public String toString() {
				final StringBuilder builder = new StringBuilder();
				builder.append('[');
				builder.append(mIsNegated ? "not " : "");
				builder.append(mTerm.toStringDirect());
				builder.append(']');
				return builder.toString();
			}
		}
		
		@Override
		public String convert(ApplicationTerm equality) {
			assert ((equality.getParameters()[0] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getFunction() == mTheory.mOr)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getParameters().length > 1)
					&& (((ApplicationTerm)equality.getParameters()[1])
							== mTheory.mTrue));
			final Term[] disjuncts = ((ApplicationTerm)equality.
					getParameters()[0]).getParameters();
			final HashMap<Term, TermNegationWrapper> disjunct2patVar =
					new HashMap<Term, TermNegationWrapper>(
							(int)((disjuncts.length - 1) / 0.75) + 1);
			final Term[] pattern = new Term[disjuncts.length];
			
			/* create disjunction object */
			final Term[] params = new Term[0];
			final Sort[] paramSorts = new Sort[0];
			final ApplicationTerm truth = mTheory.mTrue;
			final FunctionSymbol not = mTheory.mNot;
			
			int index = -1;
			int trueIndex = -1;
			boolean firstNegated = false;
			Term reasonTerm = null;
			int i = 0;
			for ( ; i < disjuncts.length; ++i) {
				Term disjunct = disjuncts[i];
				if (disjunct == truth) {
					trueIndex = i;
					pattern[i] = truth;
					++i;
					break;
				} else {
					final boolean isNegated = ((disjunct instanceof ApplicationTerm)
							&&
							((ApplicationTerm)disjunct).getFunction() == not);
					if (isNegated) {
						assert (((ApplicationTerm)disjunct).getParameters().
								length == 1);
						disjunct =
								((ApplicationTerm)disjunct).getParameters()[0];
					}
					TermNegationWrapper wrapper =
							disjunct2patVar.get(disjunct);
					if (wrapper == null) {
						wrapper = new TermNegationWrapper(
								getTerm(PATTERN_VAR_PREFIX + ++index, params,
										paramSorts), isNegated);
						disjunct2patVar.put(disjunct, wrapper);
					} else {
						// check for dual occurrence
						if (wrapper.mIsNegated ^ isNegated) {
							firstNegated = wrapper.mIsNegated;
							reasonTerm = wrapper.mTerm;
							pattern[i] = (isNegated)
									? mTheory.not(wrapper.mTerm)
									: wrapper.mTerm;
							++i;
							break;
						}
					}
					pattern[i] = (isNegated)
							? mTheory.not(wrapper.mTerm)
							: wrapper.mTerm;
				}
			}
			/*
			 * more efficient filler of the pattern, do not care what the other
			 * variables look like
			 */
			for ( ; i < disjuncts.length; ++i) {
				pattern[i] = getTerm(PATTERN_VAR_PREFIX + ++index, params,
						paramSorts);
			}
			
			assert (pattern[pattern.length - 1] != null);
			
			final String proof;
			// no 'True' before term and its negation
			if (trueIndex == -1) {
				assert (reasonTerm != null);
				if (pattern.length == 2) {
					if (firstNegated) {
						proof = "(rule HOL.simp_thms(5))\n";
					} else {
						proof = "(rule HOL.simp_thms(4))\n";
					}
				} else {
					final StringBuilder builder = new StringBuilder(128);
					if (firstNegated) {
						builder.append("(intro rw_orTaut_neg [where p = \"");
					} else {
						builder.append("(intro rw_orTaut_pos [where p = \"");
					}
					mConverter.convertToAppendable(reasonTerm, builder);
					builder.append("\"] rw_orTaut_elim, "
							+ "(erule HOL.disjI1 | rule HOL.disjI2) +)\n");
					
					proof = builder.toString();
				}
			} else {
				// 'True' before term and its negation
				// 'True' at first position, shorter proof
				if (trueIndex == 0) {
					proof = "(rule HOL.simp_thms(30))\n";
				} else if (trueIndex == disjuncts.length - 1) {
					// 'True' only at last position, extra rule needed
					proof = "(intro HOL.simp_thms(30) rw_orTaut_elim, "
							+ "rule HOL.refl)\n";
				} else {
					// 'True' at earlier position
					proof = "(intro HOL.simp_thms(30) rw_orTaut_elim)\n";
				}
			}
			
			return getMainProof(
					mTheory.term(equality.getFunction(),
							mTheory.term(mTheory.mOr, pattern),
							equality.getParameters()[1]),
					proof);
		}
	}
	
	/**
	 * This class converts the :impToOr rule.
	 * 
	 * For binary implications the proof has one argument less. 
	 */
	private class ImpToOrRule implements IRule {
		@Override
		public String convert(final ApplicationTerm equality) {
			assert ((equality.getParameters()[0] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getFunction().getName() == "=>")
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getParameters().length > 1));
			
			if (((ApplicationTerm)equality.getParameters()[0]).
							getParameters().length == 2) {
				return "(rule rw_impToOr_start, rule rw_impToOr_fin)\n";
			} else {
				return "(rule rw_impToOr_start, intro rw_impToOr_step, "
						+ "rule rw_impToOr_fin)\n";
			}
		}
	}
	
	/**
	 * This class converts the :divisible rule.
	 * 
	 * There are four cases: The dividing constant is 1, the divided term is a
	 * constant (divisible or not), and else a general rewrite.
	 */
	private class DivisibleRule implements IRule {
		@Override
		public String convert(final ApplicationTerm equality) {
			assert ((equality.getParameters()[0] instanceof ApplicationTerm)
					&& (((ApplicationTerm)equality.getParameters()[0]).
							getFunction().getIndices().length == 1));
			final Term rhs = equality.getParameters()[1];
			
			// constant divisible result
			if (rhs == mTheory.mFalse) {
				return mSimplifier.getRule() + "\n";
			} else if ((rhs == mTheory.mTrue)) {
				// every integer is divisible by 1
				if (((ApplicationTerm)equality.getParameters()[0]).
						getFunction().getIndices()[0].equals(BigInteger.ONE)) {
					return "(rule rw_divisible1)\n";
				} else {
					// constant divisible result
					return mSimplifier.getRule() + "\n";
				}
			} else {
				// normal rewrite
				return "(rule rw_divisible, " + mSimplifier.getRule() + ")\n";
			}
		}
	}
	
	/**
	 * This class converts the :div-1 rule.
	 * 
	 * The problem is to apply the correct rule according to the factor of the
	 * term being positive or negative, 1 or -1.
	 */
	private class DivM1Rule implements IRule {
		@Override
		public String convert(ApplicationTerm equality) {
			assert (equality.getParameters()[0] instanceof ApplicationTerm);
			final ApplicationTerm div =
					(ApplicationTerm)equality.getParameters()[0];
			assert ((div.getFunction().getName() == "div")
					&& (div.getParameters().length == 2));
			
			if (div.getParameters()[0] instanceof ApplicationTerm) {
				final ApplicationTerm lhs =
						(ApplicationTerm)div.getParameters()[0];
				final String function = lhs.getFunction().getName();
				if ((function == "-") && (lhs.getParameters().length == 1)) {
					return "(rule rw_divM1_neg)\n";
				} else if (function == "*") {
					assert (lhs.getParameters().length == 2);
					if (lhs.getParameters()[0] instanceof ApplicationTerm) {
						final ApplicationTerm factor =
								(ApplicationTerm)lhs.getParameters()[0];
						if ((factor.getFunction().getName() == "-")
								&& (factor.getParameters().length == 1)
								&& (factor.getParameters()[0]
										instanceof ConstantTerm)) {
							return "(rule rw_divM1_fac_neg)\n";
						}
					} else {
						return "(rule rw_divM1_fac_pos)\n";
					}
				}
			}
			
			return "(rule rw_divM1_pos)\n";
		}
	}
	
	// [end] rules //
	
	// [start] pattern lemma specific //
	
	/**
	 * This method creates a new term given the function name and the
	 * parameters.
	 * 
	 * @param name function name
	 * @param parameters parameters
	 * @param parameterSorts parameter sorts
	 * @return ApplicationTerm with the function and the parameters
	 */
	private ApplicationTerm getTerm(final String name, final Term[] parameters,
			final Sort[] parameterSorts) {
		final ApplicationTerm result = mTheory.term(name, parameters);
		
		if (result == null) {
			return mTheory.term(
					mTheory.declareFunction(
							name, parameterSorts, mTheory.getBooleanSort()),
					parameters);
		}
		
		return result;
	}
	
	/**
	 * This class wraps a pattern and the associated proof.
	 */
	private class PatternProof {
		// the pattern
		private final Term mPattern;
		// the proof
		private final String mProof;
		
		/**
		 * @param pattern the pattern
		 * @param proof the proof
		 */
		public PatternProof(final Term pattern, final String proof) {
			mPattern = pattern;
			mProof = proof;
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append('[');
			builder.append(mPattern.toStringDirect());
			builder.append(", ");
			builder.append(mProof);
			builder.deleteCharAt(builder.length() - 1);
			builder.append(']');
			return builder.toString();
		}
	}
	
	/**
	 * This method returns the proof for a pattern lemma in the main file.
	 * That is, it just uses the pattern lemma.
	 * 
	 * @param pattern the pattern term
	 * @param proof the pattern lemma proof string
	 * @return the proof string in the main file
	 */
	private String getMainProof(final Term pattern, final String proof) {
		// store pattern proof
		mLastPatternProof = new PatternProof(pattern, proof);
		
		return "(rule " + REWRITE_PREFIX + ++mLemmaNumber + ")\n";
	}
	
	/**
	 * This method writes a stored pattern lemma to the lemma appendable.
	 */
	public void writeLemma() {
		if (mLastPatternProof != null) {
			try {
				mLemmaAppendable.append("\nlemma ");
				mLemmaAppendable.append(REWRITE_PREFIX);
				mLemmaAppendable.append(Integer.toString(mLemmaNumber));
				mLemmaAppendable.append(": \"");
				mConverter.convertToAppendable(
						mLastPatternProof.mPattern, mLemmaAppendable);
				mLemmaAppendable.append("\"\nby ");
				
				mLemmaAppendable.append(mLastPatternProof.mProof);
	        } catch (final IOException e) {
	            throw new RuntimeException("Appender throws IOException", e);
	        }
			
			mLastPatternProof = null;
		}
	}
	
	/**
	 * This method forgets a stored pattern lemma.
	 */
	public void forgetLemma() {
		if (mLastPatternProof != null) {
			mLastPatternProof = null;
			--mLemmaNumber;
		}
	}
	
	// [end] pattern lemma specific //
	
	/**
	 * This method converts the rewrite rule.
	 * Many rules only need one application of a lemma.
	 * Only the :trueNotFalse, :eqSame, :distinctBool, :distinctNeg,
	 * :distinctTrue, :distinctFalse, :distinctBinary, :notSimp, :impToOr, and
	 * :divisible rules need more effort.
	 * 
	 * @param equality the rewrite equality
	 * @param annotation the specific rule that is used
	 * @return the proof rule (keywords for special cases!)
	 */
	public String convert(final ApplicationTerm equality,
			final String annotation) {
		assert (mAnnot2Rule.get(annotation) != null);
		return mAnnot2Rule.get(annotation).convert(equality);
	}
}
