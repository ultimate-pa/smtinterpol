package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class ProofRules {
	public final static String RES = "res";
	public final static String ASSUME = "assume";
	public final static String FALSEE = "false-";
	public final static String TRUEI = "true+";
	public final static String NOTI = "not+";
	public final static String NOTE = "not-";
	public final static String ORI = "or+";
	public final static String ORE = "or-";
	public final static String ANDI = "and+";
	public final static String ANDE = "and-";
	public final static String IMPI = "=>+";
	public final static String IMPE = "=>-";
	public final static String IFFI1 = "=+1";
	public final static String IFFI2 = "=+2";
	public final static String IFFE1 = "=-1";
	public final static String IFFE2 = "=-2";
	public final static String XORI = "xor+";
	public final static String XORE = "xor-";
	public final static String FORALLI = "forall+";
	public final static String FORALLE = "forall-";
	public final static String EXISTSI = "exists+";
	public final static String EXISTSE = "exists-";
	// equality chains of length >=3
	public final static String EQI = "=+";
	public final static String EQE = "=-";
	public final static String DISTINCTI = "distinct+";
	public final static String DISTINCTE = "distinct-";

	public final static String ITE1 = "ite1";
	public final static String ITE2 = "ite2";
	public final static String REFL = "refl";
	public final static String SYMM = "symm";
	public final static String TRANS = "trans";
	public final static String CONG = "cong";
	public final static String EXPAND = "expand";
	public final static String DELANNOT = "del!";
	/**
	 * sort name for proofs.
	 */
	public final static String PROOF = "Proof";
	public final static String AXIOM = "axiom";
	public final static String CHOOSE = "choose";

	public final static String PREFIX = "..";

	public final static String ANNOT_VARS = ":vars";
	public final static String ANNOT_VALUES = ":values";
	public final static String ANNOT_POS = ":pos";
	public final static String ANNOT_UNIT = ":unit";

	public ProofRules(final Theory theory) {
		mTheory = theory;
		setupTheory();
		mAxiom = theory.term(PREFIX + AXIOM);
	}

	private final Theory mTheory;
	private final Term mAxiom;

	private void setupTheory() {

		if (mTheory.getDeclaredSorts().containsKey(PREFIX + PROOF)) {
			return;
		}

		mTheory.declareInternalSort(PREFIX + PROOF, 0, 0);
		final Sort proofSort = mTheory.getSort(PREFIX + PROOF);
		final Sort boolSort = mTheory.getBooleanSort();
		final Sort[] generic = mTheory.createSortVariables("X");
		final Sort[] bool1 = new Sort[] { boolSort };
		final Sort[] sort0 = new Sort[0];

		mTheory.declareInternalFunction(PREFIX + RES, new Sort[] { boolSort, proofSort, proofSort }, proofSort, 0);
		mTheory.declareInternalFunction(PREFIX + AXIOM, sort0, proofSort, 0);
		mTheory.declareInternalFunction(PREFIX + ASSUME, bool1, proofSort, 0);
		mTheory.declareInternalPolymorphicFunction(PREFIX + CHOOSE, generic, bool1, generic[0], 0);
	}

	public Term resolutionRule(final Term pivot, final Term proofPos, final Term proofNeg) {
		return mTheory.term(PREFIX + RES, pivot, proofPos, proofNeg);
	}

	public Term asserted(final Term t) {
		return mTheory.term(PREFIX + ASSUME, t);
	}

	public Term choose(final TermVariable tv, final Term formula) {
		return mTheory.term(PREFIX + CHOOSE, mTheory.lambda(new TermVariable[] { tv }, formula));
	}

	private Annotation[] annotate(final String rule, final Term[] terms, final Annotation... moreAnnots) {
		final Annotation[] annots = new Annotation[moreAnnots.length + 1];
		annots[0] = new Annotation(rule, terms);
		System.arraycopy(moreAnnots, 0, annots, 1, moreAnnots.length);
		return annots;
	}

	public Term trueIntro(final Theory t) {
		return mTheory.annotatedTerm(annotate(":" + TRUEI, null), mAxiom);
	}

	public Term falseElim() {
		return mTheory.annotatedTerm(annotate(":" + FALSEE, null), mAxiom);
	}

	public Term notIntro(final Term notTerm) {
		assert ((ApplicationTerm) notTerm).getFunction().getName() == SMTLIBConstants.NOT;
		return mTheory.annotatedTerm(annotate(":" + NOTI, ((ApplicationTerm) notTerm).getParameters()), mAxiom);
	}

	public Term notElim(final Term notTerm) {
		assert ((ApplicationTerm) notTerm).getFunction().getName() == SMTLIBConstants.NOT;
		return mTheory.annotatedTerm(annotate(":" + NOTE, ((ApplicationTerm) notTerm).getParameters()), mAxiom);
	}

	public Term orIntro(final int pos, final Term orTerm) {
		assert ((ApplicationTerm) orTerm).getFunction().getName() == SMTLIBConstants.OR;
		return mTheory.annotatedTerm(
				annotate(":" + ORI, ((ApplicationTerm) orTerm).getParameters(), new Annotation(ANNOT_POS, pos)),
				mAxiom);
	}

	public Term orElim(final Term orTerm) {
		assert ((ApplicationTerm) orTerm).getFunction().getName() == SMTLIBConstants.OR;
		return mTheory.annotatedTerm(annotate(":" + ORE, ((ApplicationTerm) orTerm).getParameters()), mAxiom);
	}

	public Term andIntro(final Term andTerm) {
		assert ((ApplicationTerm) andTerm).getFunction().getName() == SMTLIBConstants.AND;
		return mTheory.annotatedTerm(annotate(":" + ANDI, ((ApplicationTerm) andTerm).getParameters()), mAxiom);
	}

	public Term andElim(final int pos, final Term andTerm) {
		assert ((ApplicationTerm) andTerm).getFunction().getName() == SMTLIBConstants.AND;
		return mTheory.annotatedTerm(
				annotate(":" + ANDE, ((ApplicationTerm) andTerm).getParameters(), new Annotation(ANNOT_POS, pos)),
				mAxiom);
	}

	public Term impIntro(final int pos, final Term impTerm) {
		assert ((ApplicationTerm) impTerm).getFunction().getName() == SMTLIBConstants.IMPLIES;
		return mTheory.annotatedTerm(
				annotate(":" + IMPI, ((ApplicationTerm) impTerm).getParameters(), new Annotation(ANNOT_POS, pos)),
				mAxiom);
	}

	public Term impElim(final Term impTerm) {
		assert ((ApplicationTerm) impTerm).getFunction().getName() == SMTLIBConstants.IMPLIES;
		return mTheory.annotatedTerm(annotate(":" + IMPE, ((ApplicationTerm) impTerm).getParameters()), mAxiom);
	}

	public Term iffIntro1(final Term iffTerm) {
		assert ((ApplicationTerm) iffTerm).getFunction().getName() == SMTLIBConstants.EQUALS;
		assert ((ApplicationTerm) iffTerm).getParameters().length == 2;
		assert ((ApplicationTerm) iffTerm).getParameters()[0].getSort().getName() == SMTLIBConstants.BOOL;
		return mTheory.annotatedTerm(annotate(":" + IFFI1, ((ApplicationTerm) iffTerm).getParameters()), mAxiom);
	}

	public Term iffIntro2(final Term iffTerm) {
		assert ((ApplicationTerm) iffTerm).getFunction().getName() == SMTLIBConstants.EQUALS;
		assert ((ApplicationTerm) iffTerm).getParameters().length == 2;
		assert ((ApplicationTerm) iffTerm).getParameters()[0].getSort().getName() == SMTLIBConstants.BOOL;
		return mTheory.annotatedTerm(annotate(":" + IFFI2, ((ApplicationTerm) iffTerm).getParameters()), mAxiom);
	}

	public Term iffElim1(final Term iffTerm) {
		assert ((ApplicationTerm) iffTerm).getFunction().getName() == SMTLIBConstants.EQUALS;
		assert ((ApplicationTerm) iffTerm).getParameters().length == 2;
		assert ((ApplicationTerm) iffTerm).getParameters()[0].getSort().getName() == SMTLIBConstants.BOOL;
		return mTheory.annotatedTerm(annotate(":" + IFFE1, ((ApplicationTerm) iffTerm).getParameters()), mAxiom);
	}

	public Term iffElim2(final Term iffTerm) {
		assert ((ApplicationTerm) iffTerm).getFunction().getName() == SMTLIBConstants.EQUALS;
		assert ((ApplicationTerm) iffTerm).getParameters().length == 2;
		assert ((ApplicationTerm) iffTerm).getParameters()[0].getSort().getName() == SMTLIBConstants.BOOL;
		return mTheory.annotatedTerm(annotate(":" + IFFE2, ((ApplicationTerm) iffTerm).getParameters()), mAxiom);
	}

	private Term xorAxiom(final String name, final Term[]... xorArgs) {
		assert checkXorParams(xorArgs);
		return mTheory.annotatedTerm(new Annotation[] { new Annotation(name, xorArgs) }, mAxiom);
	}

	public Term xorIntro(final Term[] xorArgs1, final Term[] xorArgs2, final Term[] xorArgs3) {
		return xorAxiom(":" + XORI, xorArgs1, xorArgs2, xorArgs3);
	}

	public Term xorElim(final Term[] xorArgs1, final Term[] xorArgs2, final Term[] xorArgs3) {
		return xorAxiom(":" + XORE, xorArgs1, xorArgs2, xorArgs3);
	}

	public Term forallIntro(final QuantifiedFormula forallTerm) {
		assert forallTerm.getQuantifier() == QuantifiedFormula.FORALL;
		return mTheory.annotatedTerm(annotate(":" + FORALLI,
				new Term[] { mTheory.lambda(forallTerm.getFreeVars(), forallTerm.getSubformula()) }), mAxiom);
	}

	public Term forallElim(final Term[] subst, final QuantifiedFormula forallTerm) {
		assert forallTerm.getQuantifier() == QuantifiedFormula.FORALL;
		return mTheory.annotatedTerm(
				annotate(":" + FORALLE,
						new Term[] { mTheory.lambda(forallTerm.getFreeVars(), forallTerm.getSubformula()) },
						new Annotation(ANNOT_VALUES, subst)),
				mAxiom);
	}

	public Term existsIntro(final Term[] subst, final QuantifiedFormula existsTerm) {
		assert existsTerm.getQuantifier() == QuantifiedFormula.EXISTS;
		return mTheory.annotatedTerm(
				annotate(":" + EXISTSI,
						new Term[] { mTheory.lambda(existsTerm.getFreeVars(), existsTerm.getSubformula()) },
						new Annotation(ANNOT_VALUES, subst)),
				mAxiom);
	}

	public Term existsElim(final Term[] subst, final QuantifiedFormula existsTerm) {
		assert existsTerm.getQuantifier() == QuantifiedFormula.EXISTS;
		return mTheory.annotatedTerm(
				annotate(":" + EXISTSE,
						new Term[] { mTheory.lambda(existsTerm.getFreeVars(), existsTerm.getSubformula()) }),
				mAxiom);
	}

	public Term equalsIntro(final Term eqTerm) {
		assert ((ApplicationTerm) eqTerm).getFunction().getName() == SMTLIBConstants.EQUALS;
		return mTheory.annotatedTerm(annotate(":" + EQI, ((ApplicationTerm) eqTerm).getParameters()), mAxiom);
	}

	public Term equalsElim(final int pos1, final int pos2, final Term eqTerm) {
		assert ((ApplicationTerm) eqTerm).getFunction().getName() == SMTLIBConstants.EQUALS;
		assert 0 <= pos1 && pos1 < ((ApplicationTerm) eqTerm).getParameters().length;
		assert 0 <= pos2 && pos2 < ((ApplicationTerm) eqTerm).getParameters().length;
		return mTheory.annotatedTerm(annotate(":" + EQE, ((ApplicationTerm) eqTerm).getParameters(),
				new Annotation(ANNOT_POS, new Integer[] { pos1, pos2 })), mAxiom);
	}

	public Term distinctIntro(final Term disTerm) {
		assert ((ApplicationTerm) disTerm).getFunction().getName() == SMTLIBConstants.DISTINCT;
		return mTheory.annotatedTerm(annotate(":" + DISTINCTI, ((ApplicationTerm) disTerm).getParameters()), mAxiom);
	}

	public Term distinctElim(final int pos1, final int pos2, final Term disTerm) {
		assert ((ApplicationTerm) disTerm).getFunction().getName() == SMTLIBConstants.DISTINCT;
		assert 0 <= pos1 && pos1 < ((ApplicationTerm) disTerm).getParameters().length;
		assert 0 <= pos2 && pos2 < ((ApplicationTerm) disTerm).getParameters().length;
		return mTheory.annotatedTerm(annotate(":" + DISTINCTE, ((ApplicationTerm) disTerm).getParameters(),
				new Annotation(ANNOT_POS, new Integer[] { pos1, pos2 })), mAxiom);
	}

	public Term refl(final Term term) {
		return mTheory.annotatedTerm(annotate(":" + REFL, new Term[] { term }), mAxiom);
	}

	public Term symm(final Term term1, final Term term2) {
		return mTheory.annotatedTerm(annotate(":" + SYMM, new Term[] { term1, term2 }), mAxiom);
	}

	public Term trans(final Term... terms) {
		assert terms.length > 2;
		return mTheory.annotatedTerm(annotate(":" + TRANS, terms), mAxiom);
	}

	public Term cong(final Term term1, final Term term2) {
		assert ((ApplicationTerm) term1).getFunction() == ((ApplicationTerm) term2).getFunction();
		assert ((ApplicationTerm) term1).getParameters().length == ((ApplicationTerm) term2).getParameters().length;
		final Annotation[] annot = new Annotation[] {
				new Annotation(":"+CONG, new Object[] {
						((ApplicationTerm) term1).getFunction(),
						((ApplicationTerm) term1).getParameters(),
						((ApplicationTerm) term2).getParameters(),
				})
		};
		return mTheory.annotatedTerm(annot, mAxiom);
	}

	public Term expand(final Term term) {
		final Annotation[] annot = new Annotation[] { new Annotation(":" + EXPAND,
				new Object[] { ((ApplicationTerm) term).getFunction(), ((ApplicationTerm) term).getParameters(), }) };
		return mTheory.annotatedTerm(annot, mAxiom);
	}

	public Term ite1(final Term iteTerm) {
		assert ((ApplicationTerm) iteTerm).getFunction().getName() == SMTLIBConstants.ITE;
		return mTheory.annotatedTerm(annotate(":" + ITE1, ((ApplicationTerm) iteTerm).getParameters()), mAxiom);
	}

	public Term ite2(final Term iteTerm) {
		assert ((ApplicationTerm) iteTerm).getFunction().getName() == SMTLIBConstants.ITE;
		return mTheory.annotatedTerm(annotate(":" + ITE2, ((ApplicationTerm) iteTerm).getParameters()), mAxiom);
	}

	public Term delAnnot(final AnnotatedTerm annotTerm) {
		final Annotation[] termAnnots = annotTerm.getAnnotations();
		final Annotation[] annots = new Annotation[termAnnots.length + 1];
		annots[0] = new Annotation(":" + DELANNOT, annotTerm.getSubterm());
		System.arraycopy(termAnnots, 0, annots, 1, termAnnots.length);
		return mTheory.annotatedTerm(annots, mAxiom);
	}

	public void printProof(final Appendable appender, final Term proof) {
		new PrintProof().append(appender, proof);
	}

	public static boolean checkXorParams(final Term[][] xorArgs) {
		assert xorArgs.length == 3;
		final HashSet<Term> xorSum = new HashSet<>();
		for (final Term[] args : xorArgs) {
			for (final Term arg : args) {
				if (xorSum.contains(arg)) {
					xorSum.remove(arg);
				} else {
					xorSum.add(arg);
				}
			}
		}
		return xorSum.isEmpty();
	}

	public boolean isAxiom(final Term proof) {
		return proof instanceof AnnotatedTerm && ((AnnotatedTerm) proof).getSubterm() == mAxiom;
	}

	public boolean isProofRule(final String rule, final Term proof) {
		return proof instanceof ApplicationTerm
				&& ((ApplicationTerm) proof).getFunction().getName().equals(PREFIX + rule);
	}

	public static class PrintProof extends PrintTerm {
		private void addChildParams(final Term child, final String expected) {
			if (child instanceof ApplicationTerm) {
				final ApplicationTerm subterm = (ApplicationTerm) child;
				assert subterm.getFunction().getName() == expected;
				final Term[] subParams = subterm.getParameters();
				for (int i = subParams.length - 1; i >= 0; i--) {
					mTodo.add(subParams[i]);
					mTodo.add(" ");
				}
			} else {
				mTodo.add(child);
				mTodo.add(" ::");
			}
		}

		private void addXorParams(final Term child) {
			mTodo.add(")");
			if (child instanceof AnnotatedTerm) {
				assert ((AnnotatedTerm) child).getAnnotations()[0].getKey() == ANNOT_UNIT;
				mTodo.add(((AnnotatedTerm) child).getSubterm());
			} else if (child instanceof ApplicationTerm) {
				final ApplicationTerm subterm = (ApplicationTerm) child;
				assert subterm.getFunction().getName() == SMTLIBConstants.XOR;
				final Term[] subParams = subterm.getParameters();
				for (int i = subParams.length - 1; i >= 1; i--) {
					mTodo.add(subParams[i]);
					mTodo.add(" ");
				}
				mTodo.add(subParams[0]);
			} else {
				mTodo.add(child);
				mTodo.add("::");
			}
			mTodo.add(" (");
		}

		@Override
		public void walkTerm(final Term proof) {
			if (proof instanceof AnnotatedTerm) {
				final AnnotatedTerm annotTerm = (AnnotatedTerm) proof;
				final Annotation[] annots = annotTerm.getAnnotations();
				if (annotTerm.getSubterm() instanceof ApplicationTerm
						&& ((ApplicationTerm) annotTerm.getSubterm()).getFunction().getName() == PREFIX + AXIOM) {
					switch (annots[0].getKey()) {
					case ":" + NOTI:
					case ":" + NOTE:
					case ":" + ORE:
					case ":" + ANDI:
					case ":" + IMPE:
					case ":" + IFFI1:
					case ":" + IFFI2:
					case ":" + IFFE1:
					case ":" + IFFE2:
					case ":" + REFL:
					case ":" + SYMM:
					case ":" + TRANS:
					case ":" + EQI:
					case ":" + DISTINCTI: {
						final Term[] params = (Term[]) annots[0].getValue();
						assert annots.length == 1;
						mTodo.add(")");
						for (int i = params.length - 1; i >= 0; i--) {
							mTodo.add(params[i]);
							mTodo.add(" ");
						}
						mTodo.add("(" + annots[0].getKey().substring(1));
						return;
					}
					case ":" + ORI:
					case ":" + ANDE:
					case ":" + IMPI: {
						final Term[] params = (Term[]) annots[0].getValue();
						assert annots.length == 2;
						assert annots[1].getKey() == ANNOT_POS;
						mTodo.add(")");
						for (int i = params.length - 1; i >= 0; i--) {
							mTodo.add(params[i]);
							mTodo.add(" ");
						}
						mTodo.add(annots[1].getValue());
						mTodo.add("(" + annots[0].getKey().substring(1) + " ");
						return;
					}
					case ":" + EQE:
					case ":" + DISTINCTE: {
						final Term[] params = (Term[]) annots[0].getValue();
						assert annots.length == 2;
						assert annots[1].getKey() == ANNOT_POS;
						final Integer[] positions = (Integer[]) annots[1].getValue();
						mTodo.add(")");
						for (int i = params.length - 1; i >= 0; i--) {
							mTodo.add(params[i]);
							mTodo.add(" ");
						}
						mTodo.add(positions[0] + " " + positions[1]);
						mTodo.add("(" + annots[0].getKey().substring(1) + " ");
						return;
					}
					case ":" + CONG: {
						assert annots.length == 1;
						final Object[] congArgs = (Object[]) annots[0].getValue();
						assert congArgs.length == 3;
						final FunctionSymbol func = (FunctionSymbol) congArgs[0];
						final Term[] params1 = (Term[]) congArgs[1];
						final Term[] params2 = (Term[]) congArgs[2];
						mTodo.add("))");
						for (int i = params2.length - 1; i >= 0; i--) {
							mTodo.add(params2[i]);
							mTodo.add(" ");
						}
						mTodo.add(func.getApplicationString());
						mTodo.add(") (");
						for (int i = params1.length - 1; i >= 0; i--) {
							mTodo.add(params1[i]);
							mTodo.add(" ");
						}
						mTodo.add(func.getApplicationString());
						mTodo.add("(" + annots[0].getKey().substring(1) + " (");
						return;
					}
					case ":" + XORI:
					case ":" + XORE: {
						assert annots.length == 1;
						final Term[][] xorLists = (Term[][]) annots[0].getValue();
						assert xorLists.length == 3;
						mTodo.add(")");
						for (int i = 2; i >= 0; i--) {
							mTodo.add(")");
							for (int j = xorLists[i].length - 1; j >= 0; j--) {
								mTodo.add(xorLists[i][j]);
								if (j > 0) {
									mTodo.add(" ");
								}
							}
							mTodo.add(" (");
						}
						mTodo.add("(" + annots[0].getKey().substring(1));
						return;
					}
					case ":" + FORALLE:
					case ":" + EXISTSI: {
						assert annots.length == 2;
						final Term[] params = (Term[]) annots[0].getValue();
						final LambdaTerm lambda = (LambdaTerm) params[0];
						final TermVariable[] termVars = lambda.getVariables();
						assert annots[1].getKey() == ANNOT_VALUES;
						final Term[] values = (Term[]) annots[1].getValue();
						mTodo.add(")");
						mTodo.add(lambda.getSubterm());
						mTodo.add(") ");
						for (int i = termVars.length; i >= 0; i--) {
							mTodo.add(")");
							mTodo.add(values[i]);
							mTodo.add(" ");
							mTodo.add(termVars[i]);
							mTodo.add(i == 0 ? "(" : " (");
						}
						mTodo.add("(" + annots[0].getKey().substring(1) + " (");
						return;
					}
					case ":" + FORALLI:
					case ":" + EXISTSE: {
						assert annots.length == 1;
						final Term[] params = (Term[]) annots[0].getValue();
						final LambdaTerm lambda = (LambdaTerm) params[0];
						final TermVariable[] termVars = lambda.getVariables();

						mTodo.add(")");
						mTodo.add(lambda.getSubterm());
						mTodo.add(") ");
						for (int i = termVars.length; i >= 0; i--) {
							mTodo.add(")");
							mTodo.add(termVars[i].getSort());
							mTodo.add(" ");
							mTodo.add(termVars[i]);
							mTodo.add(i == 0 ? "(" : " (");
						}
						mTodo.add("(" + annots[0].getKey().substring(1) + " (");
						return;
					}
					case ":" + DELANNOT: {
						mTodo.add("))");
						final Term term = (Term) annots[0].getValue();
						for (int i = annots.length - 1; i >= 1; i--) {
							if (annots[i].getValue() != null) {
								mTodo.addLast(annots[i].getValue());
								mTodo.addLast(" ");
							}
							mTodo.addLast(" " + annots[i].getKey());
						}
						mTodo.addLast(term);
						mTodo.add("(" + DELANNOT + " (! ");
						return;
					}
					}
				}
			}

			if (proof instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) proof;
				final Term[] params = appTerm.getParameters();
				switch (appTerm.getFunction().getName()) {
				case PREFIX + RES: {
					assert params.length == 3;
					mTodo.add(")");
					for (int i = params.length - 1; i >= 0; i--) {
						mTodo.add(params[i]);
						mTodo.add(" ");
					}
					mTodo.add("(" + RES);
					return;
				}
				case PREFIX + ASSUME: {
					assert params.length == 1;
					mTodo.add(")");
					mTodo.add(params[0]);
					mTodo.add("(" + ASSUME + " ");
					return;
				}
				default:
					break;
				}
			}
			super.walkTerm(proof);
		}
	}
}
