/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

/**
 * @author Markus
 *
 */
public interface IRuleApplicator {
	
	
	/**
	 * @param orig
	 * @return
	 */
	public Term expand(ApplicationTerm orig);
	/**
	 * Track the expand definition rule.
	 * @param orig The original term.
	 * @param res  The result of the expansion.
	 * @return
	 */
	public Term expandDef(Term orig, Term res);
	/**
	 * Track an equality rewrite.
	 * @param args The arguments to the equality.
	 * @param res  The result of the rewrite.
	 * @param rule The number of the rule used.
	 * @return
	 */
	public Term equality(Term[] args, Object res, int rule);
	/**
	 * Track a distinct rewrite.
	 * @param args The arguments to the distinct.
	 * @param res  The result of the rewrite.
	 * @param rule The number of the rule used.
	 * @return
	 */
	public Term distinct(Term[] args, Term res, int rule);
	/**
	 * Track the transformation of a Boolean distinct into a negated equality.
	 * @param lhs          The left-hand-side of the distinct.
	 * @param rhs          The right-hand-side of the distinct.
	 * @param firstNegated Should the lhs be negated?
	 * @return
	 */
	public Term distinctBoolEq(Term lhs, Term rhs, boolean firstNegated);
	/**
	 * Track the result of a negation rewrite.
	 * @param pos  What to negate.
	 * @param res  The result of the rewrite.
	 * @param rule The number of the rule.
	 * @return
	 */
	public Term negation(Term pos, Term res, int rule);
	/**
	 * Track an or rewrite
	 * @param args The arguments to the disjunction.
	 * @param res  The simplification result.
	 * @param rule The rule number.
	 * @return
	 */
	public Term or(Term[] args, Term res, int rule);
	/**
	 * Track an ite rewrite.
	 * @param cond     The condition.
	 * @param thenTerm The then-term.
	 * @param elseTerm The else-term.
	 * @param res      The result.
	 * @param rule     The rule number.
	 * @return
	 */
	public Term ite(Term cond, Term thenTerm, Term elseTerm, Term res, int rule);
	/**
	 * Track removal of a Boolean connective.
	 * @param origArgs The original term.
	 * @param result   (Part of) the resulting term (used for SMTAffineTerms).
	 * @param rule The rule number.
	 * @return
	 */
	public Term removeConnective(Term[] origArgs, Term result, int rule);
	/**
	 * Track an annotation stripping.
	 * @param orig The annotated term.
	 * @return
	 */
	public Term strip(AnnotatedTerm orig);
	/**
	 * Track a canonical summarization.
	 * @param fsym The function symbol of the original term.
	 * @param args The arguments of the original term.
	 * @param res  The result of the rewrite.
	 * @return
	 */
	public Term sum(FunctionSymbol fsym, Term[] args, Term res);
	/**
	 * Track a normalization of a constant term.  This rule is needed, e.g., to
	 * justify the transformation of 1.5 into (/ 3 2).
	 * @param term The constant.
	 * @param res  The result of the transformation.
	 * @return
	 */
	public Term normalized(ConstantTerm term, SMTAffineTerm res);
	/**
	 * Track a transformation into <=0-form.
	 * @param orig The original term.
	 * @param leq  The resulting term.
	 * @param rule The rule applied.
	 * @return
	 */
	public Term toLeq0(Term orig, SMTAffineTerm leq, int rule);
	/**
	 * Track an leq simplification.
	 * @param leq  The leq0-term.
	 * @param res  The rewrite result.
	 * @param rule The simplification rule.
	 * @return
	 */
	public Term leqSimp(SMTAffineTerm leq, Term res, int rule);
	/**
	 * Track an application of the IRA-Hack.
	 * @param orig     The original term.
	 * @param origArgs Arguments that should be used for the original term.
	 * @param newArgs  The arguments to that term after applying the IRA-Hack.
	 * @return
	 */
	public Term desugar(ApplicationTerm orig, Term[] origArgs, Term[] newArgs);
	/**
	 * Track a modulo-rewrite. (mod x y) ==> (- x  (* y (div x y))) under the
	 * assumption y is integral and not 0.
	 * @param appTerm The modulo application term.
	 * @param res     The resulting term.
	 * @return
	 */
	public Term modulo(ApplicationTerm appTerm, Term res);
	/**
	 * Track a modulo simplification, i.e., a rewrite that does not transform
	 * a modulo into an application term like 
	 * {@link #modulo(ApplicationTerm, Term)}, but evaluates applications
	 * (mod x y) where either y is 1 or -1, or x is constant.
	 * @param x    The first argument of the mod.
	 * @param y    The second argument of the mod.
	 * @param res  The result of the rule.
	 * @param rule The simplification rule applied.
	 * @return
	 */
	public Term mod(Term x, Term y, Term res, int rule);
	/**
	 * Track a divison simplification, i.e., a rewrite that evaluates
	 * applications (div x y) where either y is 1 or -1, or x is constant.
	 * @param x    The first argument of the div.
	 * @param y    The second argument of the div.
	 * @param res  The result of the rule.
	 * @param rule The simplification rule applied.
	 * @return
	 */
	public Term div(Term x, Term y, Term res, int rule);
	/**
	 * Track a divisible-rewrite.  ((_ divisible n) x) ==> (= x (* n (div x n))).
	 * @param divn The divisible-by-n symbol.
	 * @param div  The divisible term.
	 * @param res  The rewritten result.
	 * @return
	 */
	public Term divisible(FunctionSymbol divn, Term div, Term res);
	/**
	 * Track a to_int simplification where the argument is constant.
	 * @param arg The argument.
	 * @param res The result.
	 * @return
	 */
	public Term toInt(Term arg, Term res);
	/**
	 * Track a to_real simplification where the argument is constant.
	 * @param arg The argument.
	 * @param res The result.
	 * @return
	 */
	public Term toReal(Term arg, Term res);
	/**
	 * Track an array rewrite.
	 * @param args   The arguments of the original array.
	 * @param result The result of the rewrite.
	 * @param rule   The rule used.
	 * @return
	 */
	public Term arrayRewrite(Term[] args, Term result, int rule);
	/**
	 * Rewrite for "useless store": (= a (store a i v)).
	 * @param store      The store term.
	 * @param result     The result of the rewrite.
	 * @param arrayFirst Is the array the lhs?
	 * @return
	 */
	public Term storeRewrite(ApplicationTerm store, Term result, boolean arrayFirst);
	
	//// ==== Tracking of clausification ====
	
	/**
	 * Track the introduction of a quote.
	 * @param orig  The original term.
	 * @param quote The quoted term.
	 * @return
	 */
	public Term quoted(Term orig, Literal quote);
	/**
	 * Track an equality interning.
	 * @param lhs The left-hand-side.
	 * @param rhs The right-hand-side.
	 * @param res The result.
	 * @return
	 */
	public Term eq(Term lhs, Term rhs, Term res);
	/**
	 * Convenience function to prevent term creation of equality terms if
	 * proof generation is disabled.
	 * @param lhs    The left-hand-side.
	 * @param rhs    The right-hand-side.
	 * @param eqAtom The equality atom.
	 * @return
	 */
	public Term eq(Term lhs, Term rhs, DPLLAtom eqAtom);
	/**
	 * Convenience function to prevent creation of leq0 terms if proof
	 * generation is disabled.
	 * @param sum The sum to be less than or equal to 0.
	 * @param lit The resulting literal.
	 * @return
	 */
	public Term leq0(SMTAffineTerm sum, Literal lit);
	/**
	 * Track literal creation.
	 * @param term The term transformed into a literal.
	 * @param lit  The resulting literal.
	 * @return
	 */
	public Term intern(Term term, Literal lit);
	/**
	 * Apply double negation elimination on a literal.  Note that the literal
	 * has to be negated already.
	 * @param lit    The literal to negate
	 * @param theory The theory to use in conversion.
	 * @return
	 */
	public Term negateLit(Literal lit, Theory theory);
	/**
	 * Apply disjunction flattening.
	 * @param args   The term to flatten.
	 * @param simpOr Apply disjunction simplification on the flattened and
	 *               interned clause.
	 * @return
	 */
	public Term flatten(Term[] args, boolean simpOr);
	/**
	 * Prepend a disjunction simplification step.
	 * @param args The disjunction to simplify.
	 * @return
	 */
	public Term orSimpClause(Term[] args);
	/**
	 * @param a
	 * @return The term a annotated with a proof (= a a)
	 */
	public Term reflexivity(Term a);
	/**
	 * @param a Annotated with a proof (= x a)
	 * @param b Annotated with a proof (= a b)
	 * @return Term b annotated with a proof (= x b)
	 */
	public Term transitivity(Term a, Term b);
	/**
	 * @param a
	 * @param b
	 * @return
	 */
	public Term congruence(Term a, Term b);
	
	
	// TODO *******************************************************************
	
	
	/**
	 * Create a clause-creation proof.
	 * @param proof The proof whose result is transformed into a clause.
	 * @return The clause conversion proof.
	 */
	public Term clause(Term proof);
	/**
	 * Create aux axiom input (tautologies).
	 * @param auxKind The kind of the aux axiom.
	 * @param auxLit  The term auxiliary literal.
	 * @param data    Data needed to construct the result term.
	 * @param base    Base used for Term-ITEs.
	 * @param auxData Auxiliary data (needed for Term-ITEs).
	 * @return Proof node of the auxiliary tautology.
	 */
	public Term auxAxiom(int auxKind, Literal auxLit, Term data, Term base,
			Object auxData);
	/**
	 * Track a structural splitting step.
	 * @param data      Data used to produce the result of the split.
	 * @param proof     The proof for the formula being split.
	 * @param splitKind The kind of split (@see ProofConstants).
	 * @return The proof for the split.
	 */
	public Term split(Term data, Term proof, int splitKind);
	
	//// ===== Accessors ====
	/**
	 * Get a rewrite proof justifying the rewrites from <code>asserted</code>
	 * into <code>result</code>.
	 * 
	 * Note that <code>asserted</code> is a Boolean term from the input.  If a
	 * proof should be produced, it has to be wrapped by the
	 * <code>@asserted</code> function.  The <code>result</code> might contain
	 * SMTAffineTerms. 
	 * @param asserted The input term.
	 * @return The rewrite proof or <code>null</code> if proof-production is
	 *         disabled.
	 */
	public Term getRewriteProof(Term asserted);
	/**
	 * Prepare to apply the IRA-Hack.  This should return a copy of the original
	 * arguments to ensure correct applications of the desugar rule.
	 * @param args The original arguments.
	 * @return <code>null</code> if no desugar should be applied and a copy of
	 *         the argument otherwise. 
	 */
	public Term[] prepareIRAHack(Term[] args);
	/**
	 * Mark the position where a clause simplification rule can be applied.
	 * This function is necessary since clause simplification is delayed and,
	 * hence, recognized at the wrong time. 
	 */
	public Term[] produceAuxAxiom(Literal auxlit, Term... args);
	/**
	 * Save the current position in the rewrite list.
	 */
	public boolean notifyLiteral(Literal lit, Term t);


}
