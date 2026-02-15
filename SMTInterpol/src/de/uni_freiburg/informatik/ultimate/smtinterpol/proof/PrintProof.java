package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Print a proof term.
 */
public class PrintProof extends PrintTerm {
	@Override
	public void walkTerm(final Term proof) {
		if (proof instanceof AnnotatedTerm) {
			final AnnotatedTerm annotTerm = (AnnotatedTerm) proof;
			final Annotation[] annots = annotTerm.getAnnotations();
			if (annots.length == 1
					&& (annots[0].getKey() == ProofRules.ANNOT_DEFINE_FUN || annots[0].getKey() == ProofRules.ANNOT_REFINE_FUN)) {
				final Object[] annotVal = (Object[]) annots[0].getValue();
				assert annotVal.length == 2;
				final FunctionSymbol func = (FunctionSymbol) annotVal[0];
				Term definition = (Term) annotVal[1];
				TermVariable[] vars;
				if (definition instanceof LambdaTerm) {
					final LambdaTerm lambda = (LambdaTerm) definition;
					definition = lambda.getSubterm();
					vars = lambda.getVariables();
				} else {
					vars = new TermVariable[0];
				}
				mTodo.add(")");
				mTodo.add(annotTerm.getSubterm());
				mTodo.add(" ");
				mTodo.add(")");
				mTodo.add(definition);
				mTodo.add(") ");
				for (int i = vars.length - 1; i >= 0; i--) {
					mTodo.add(")");
					mTodo.add(vars[i].getSort());
					mTodo.add(" ");
					mTodo.add(vars[i]);
					mTodo.add(i == 0 ? "(" : " (");
				}
				mTodo.add(" (");
				mTodo.add(func.getApplicationString());
				mTodo.add("((" + annots[0].getKey().substring(1) + " ");
				return;
			} else if (annots.length == 1 && annots[0].getKey() == ProofRules.ANNOT_DECLARE_FUN) {
				final Object[] annotVal = (Object[]) annots[0].getValue();
				assert annotVal.length == 1;
				final FunctionSymbol func = (FunctionSymbol) annotVal[0];
				mTodo.add(")");
				mTodo.add(annotTerm.getSubterm());
				mTodo.add(" ");
				mTodo.add(")");
				mTodo.add(func.getReturnSort());
				mTodo.add(") ");
				final Sort[] paramSorts = func.getParameterSorts();
				for (int i = paramSorts.length - 1; i >= 0; i--) {
					mTodo.add(paramSorts[i]);
					if (i > 0) {
						mTodo.add(" ");
					}
				}
				mTodo.add(" (");
				mTodo.add(func.getApplicationString());
				mTodo.add("((" + annots[0].getKey().substring(1) + " ");
				return;
			} else if (annotTerm.getSubterm() instanceof ApplicationTerm
					&& ((ApplicationTerm) annotTerm.getSubterm()).getFunction().getName() == ProofRules.PREFIX + ProofRules.AXIOM) {
				switch (annots[0].getKey()) {
				case ":" + ProofRules.ORACLE: {
					assert annots.length >= 1;
					final Object[] clause = (Object[]) annots[0].getValue();
					mTodo.add(")");
					for (int i = annots.length - 1; i >= 1; i--) {
						if (annots[i].getValue() != null) {
							mTodo.add(annots[i].getValue());
							mTodo.add(" ");
						}
						mTodo.add(annots[i].getKey());
						mTodo.add(" ");
					}
					mTodo.add(clause);
					mTodo.add("(" + annots[0].getKey().substring(1) + " ");
					return;
				}
				case ":" + ProofRules.TRUEI:
				case ":" + ProofRules.FALSEE: {
					assert annots.length == 1;
					assert annots[0].getValue() == null;
					mTodo.add(annots[0].getKey().substring(1));
					return;
				}
				case ":" + ProofRules.NOTI:
				case ":" + ProofRules.NOTE:
				case ":" + ProofRules.ORE:
				case ":" + ProofRules.ANDI:
				case ":" + ProofRules.IMPE:
				case ":" + ProofRules.IFFI1:
				case ":" + ProofRules.IFFI2:
				case ":" + ProofRules.IFFE1:
				case ":" + ProofRules.IFFE2:
				case ":" + ProofRules.ITE1:
				case ":" + ProofRules.ITE2:
				case ":" + ProofRules.EQI:
				case ":" + ProofRules.FORALLI:
				case ":" + ProofRules.EXISTSE:
				case ":" + ProofRules.EXPAND:
				case ":" + ProofRules.DISTINCTI:
				case ":" + ProofRules.DELANNOT:
				case ":" + ProofRules.BVLITERAL:
				case ":" + ProofRules.UBV2INT2BV: {
					assert annots.length == 1;
					mTodo.add(")");
					mTodo.add(annots[0].getValue());
					mTodo.add("(" + annots[0].getKey().substring(1) + " ");
					return;
				}

				case ":" + ProofRules.XORI:
				case ":" + ProofRules.XORE:
				case ":" + ProofRules.REFL:
				case ":" + ProofRules.SYMM:
				case ":" + ProofRules.TRANS:
				case ":" + ProofRules.CONG:
				case ":" + ProofRules.TRICHOTOMY:
				case ":" + ProofRules.TOTAL:
				case ":" + ProofRules.TOTALINT:
				case ":" + ProofRules.POLYADD:
				case ":" + ProofRules.POLYMUL:
				case ":" + ProofRules.MULPOS:
				case ":" + ProofRules.DIVIDEDEF:
				case ":" + ProofRules.TOREALDEF:
				case ":" + ProofRules.TOINTLOW:
				case ":" + ProofRules.TOINTHIGH:
				case ":" + ProofRules.DIVLOW:
				case ":" + ProofRules.DIVHIGH:
				case ":" + ProofRules.MODDEF:
				case ":" + ProofRules.SELECTSTORE1:
				case ":" + ProofRules.SELECTSTORE2:
				case ":" + ProofRules.EXTDIFF:
				case ":" + ProofRules.CONST:
				case ":" + ProofRules.DT_PROJECT:
				case ":" + ProofRules.DT_CONS:
				case ":" + ProofRules.DT_TESTI:
				case ":" + ProofRules.DT_EXHAUST:
				case ":" + ProofRules.DT_MATCH:
				case ":" + ProofRules.DT_TESTE:
				case ":" + ProofRules.DT_ACYCLIC: {
					assert annots.length == 1;
					final Object[] params = (Object[]) annots[0].getValue();
					mTodo.add(")");
					for (int i = params.length - 1; i >= 0; i--) {
						mTodo.add(params[i]);
						mTodo.add(" ");
					}
					mTodo.add("(" + annots[0].getKey().substring(1));
					return;
				}
				case ":" + ProofRules.ORI:
				case ":" + ProofRules.ANDE:
				case ":" + ProofRules.IMPI: {
					final Term param = (Term) annots[0].getValue();
					assert annots.length == 2;
					assert annots[1].getKey() == ProofRules.ANNOT_POS;
					mTodo.add(")");
					mTodo.add(param);
					mTodo.add(" ");
					mTodo.add(annots[1].getValue());
					mTodo.add("(" + annots[0].getKey().substring(1) + " ");
					return;
				}
				case ":" + ProofRules.BVCONST: {
					final Term param = (Term) annots[0].getValue();
					assert annots.length == 2;
					assert annots[1].getKey() == ProofRules.ANNOT_BVLEN;
					mTodo.add(")");
					mTodo.add(annots[1].getValue());
					mTodo.add(" ");
					mTodo.add(param);
					mTodo.add("(" + annots[0].getKey().substring(1) + " ");
					return;
				}
				case ":" + ProofRules.INT2UBV2INT:
				case ":" + ProofRules.INT2SBV2INT: {
					final Term param = (Term) annots[0].getValue();
					assert annots.length == 2;
					assert annots[1].getKey() == ProofRules.ANNOT_BVLEN;
					mTodo.add(")");
					mTodo.add(param);
					mTodo.add(" ");
					mTodo.add(annots[1].getValue());
					mTodo.add("(" + annots[0].getKey().substring(1) + " ");
					return;
				}
				case ":" + ProofRules.EQE:
				case ":" + ProofRules.DISTINCTE: {
					final Term param = (Term) annots[0].getValue();
					assert annots.length == 2;
					assert annots[1].getKey() == ProofRules.ANNOT_POS;
					final Integer[] positions = (Integer[]) annots[1].getValue();
					mTodo.add(")");
					mTodo.add(param);
					mTodo.add(" ");
					mTodo.add(positions[0] + " " + positions[1]);
					mTodo.add("(" + annots[0].getKey().substring(1) + " ");
					return;
				}
				case ":" + ProofRules.FORALLE:
				case ":" + ProofRules.EXISTSI: {
					assert annots.length == 2;
					final Term quant = (Term) annots[0].getValue();
					assert annots[1].getKey() == ProofRules.ANNOT_VALUES;
					final Term[] values = (Term[]) annots[1].getValue();
					mTodo.add(")");
					mTodo.add(quant);
					mTodo.add(") ");
					for (int i = values.length - 1; i >= 0; i--) {
						mTodo.add(values[i]);
						if (i > 0) {
							mTodo.add(" ");
						}
					}
					mTodo.add("(" + annots[0].getKey().substring(1) + " (");
					return;
				}
				case ":" + ProofRules.FARKAS: {
					final Term[] params = (Term[]) annots[0].getValue();
					assert annots.length == 2;
					assert annots[1].getKey() == ProofRules.ANNOT_COEFFS;
					final BigInteger[] coeffs = (BigInteger[]) annots[1].getValue();
					assert params.length == coeffs.length;
					mTodo.add(")");
					for (int i = params.length - 1; i >= 0; i--) {
						mTodo.add(params[i]);
						mTodo.add(" ");
						mTodo.add(coeffs[i]);
						mTodo.add(" ");
					}
					mTodo.add("(" + annots[0].getKey().substring(1));
					return;
				}
				}
			}
		}

		if (proof instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) proof;
			final Term[] params = appTerm.getParameters();
			switch (appTerm.getFunction().getName()) {
			case ProofRules.PREFIX + ProofRules.RES: {
				assert params.length == 3;
				mTodo.add(")");
				for (int i = params.length - 1; i >= 0; i--) {
					mTodo.add(params[i]);
					mTodo.add(" ");
				}
				mTodo.add("(" + ProofRules.RES);
				return;
			}
			case ProofRules.PREFIX + ProofRules.CHOOSE: {
				assert params.length == 1;
				final LambdaTerm lambda = (LambdaTerm) params[0];
				assert lambda.getVariables().length == 1;
				mTodo.add(")");
				mTodo.add(lambda.getSubterm());
				mTodo.add(") ");
				mTodo.add(lambda.getVariables()[0].getSort());
				mTodo.add(" ");
				mTodo.add(lambda.getVariables()[0]);
				mTodo.add("(" + ProofRules.CHOOSE + " (");
				return;
			}
			case ProofRules.PREFIX + ProofRules.ASSUME: {
				assert params.length == 1;
				mTodo.add(")");
				mTodo.add(params[0]);
				mTodo.add("(" + ProofRules.ASSUME + " ");
				return;
			}
			default:
				break;
			}
		}

		if (proof instanceof LetTerm) {
			final LetTerm let = (LetTerm) proof;
			final TermVariable[] vars = let.getVariables();
			final Term[] values = let.getValues();
			boolean hasLetProof = false;
			boolean hasLetTerm = false;
			for (int i = 0; i < vars.length; i++) {
				if (ProofRules.isProof(values[i])) {
					hasLetProof = true;
				} else {
					hasLetTerm = true;
				}
			}
			// close parentheses
			if (hasLetTerm) {
				mTodo.addLast(")");
			}
			if (hasLetProof) {
				mTodo.addLast(")");
			}
			// Add subterm to stack.
			mTodo.addLast(let.getSubTerm());
			// add the let-proof for proof variables.
			if (hasLetProof) {
				// Add subterm to stack.
				// Add assigned values to stack
				String sep = ")) ";
				for (int i = values.length - 1; i >= 0; i--) {
					if (ProofRules.isProof(values[i])) {
						mTodo.addLast(sep);
						mTodo.addLast(values[i]);
						mTodo.addLast("(" + vars[i].toString() + " ");
						sep = ") ";
					}
				}
				mTodo.addLast("(let-proof (");
			}
			// add the let for non-proof variables.
			if (hasLetTerm) {
				// Add assigned values to stack
				String sep = ")) ";
				for (int i = values.length - 1; i >= 0; i--) {
					if (!ProofRules.isProof(values[i])) {
						mTodo.addLast(sep);
						mTodo.addLast(values[i]);
						mTodo.addLast("(" + vars[i].toString() + " ");
						sep = ") ";
					}
				}
				mTodo.addLast("(let (");
			}
			return;
		}
		super.walkTerm(proof);
	}
}