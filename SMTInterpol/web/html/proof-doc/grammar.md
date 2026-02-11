
## Grammar

The grammar for proofs uses the grammar for ⟨numeral⟩, ⟨term⟩,
⟨sort⟩, ⟨symbol⟩, ⟨sorted_var⟩, ⟨attribute⟩ from the SMT-LIB standard,
version 2.6.  It is given below:

```
⟨term_or_proof⟩ ::= ⟨term⟩ | ⟨proof⟩
⟨polarity⟩ ::= + | -
⟨literal⟩ ::= ⟨polarity⟩ ⟨term⟩
⟨clause⟩ ::= ( ⟨literal⟩ ⃰ )
⟨proof⟩ ::= (res ⟨term⟩ ⟨proof⟩ ⟨proof⟩)
          | (let ((⟨symbol⟩ ⟨term⟩)⁺) ⟨proof⟩)
          | (let-proof ((⟨symbol⟩ ⟨proof⟩)⁺) ⟨proof⟩)
          | ⟨symbol⟩
          | ((define-fun ⟨symbol⟩ (⟨sorted_var⟩⁺) ⟨sort⟩ ⟨term⟩) ⟨proof⟩)
          | ((declare-fun ⟨symbol⟩ (⟨sort⟩⁺) ⟨sort⟩) ⟨proof⟩)
          | ((refine-fun ⟨symbol⟩ (⟨sorted_var⟩⁺) ⟨sort⟩ ⟨term⟩) ⟨proof⟩)
          | (assume ⟨term⟩)
          | (oracle ⟨clause⟩ ⟨attributes⟩ ⃰)
          | ⟨core-axiom⟩
          | ⟨arith-axiom⟩
          | ⟨datatype-axiom⟩
          | ⟨bitvector-axiom⟩
```

In our settings, an atom is an SMT-LIB term.  A literal is a term with
a polarity + or -.  A clause is a set of literal, written as a
sequence with a pair of parenthesis around it.

Every proof proves a clause.  The whole proof given by an SMT-solver
as the solution, should prove the empty clause.  A proof may be
produced from subproofs and for this purpose a subproof may be bound
to a variable symbol, so it can be efficiently used multiple times.

The rule `(res t p1 p2)` is the resolution rule, the main work-horse
of this proof format.  Here `p1` is a proof that proves some clause
$C_1$ and `p2` a proof that proves $C_2$.  The side-condition is that
`+ t` occurs in $C_1$ and `- t` in $C_2$ (the order of the arguments `p1`

and `p2` is important).  The resulting proof term proves the clause
$(C_1\setminus \{+ t\}) \cup (C_2\setminus\{- t\})$.

The let binder `let ((x t)) p` binds the value of `t` to a symbol
`x`. Here `t` can be an arbitrary term.  The symbol `x` can then be
used in terms as free variable.  Similarly, the let binder `let-proof
((x p1)) p` binds a proof `p1` to the variable `x` and `x` can be
referenced in `p` using the ⟨symbol⟩ rule.  The scope of `x` is the
proof `p` and the resulting proof proves the same clause as `p`.

Proofs can also contain `define-fun` with the same syntax as in
SMT-LIB. These will define the function symbol for the subproof, which
can use the definition using the `expand` axiom.  The defined function
symbol must not be used outside the subproof.  Similarly,
`declare-fun` will add an uninterpreted function.

There is also a `refine-fun` which adds a function definition to an
already declared function.  It is only allowed on the outermost layer
of satisfiability proofs and is used to fix the model for
uninterpreted function occuring in the benchmark.

The rule `(assume t)` where `t` is a term, proves the unit
clause `(+ t)`.  Its side condition (checked by the proof checker) is
that it was asserted in the input problem by an SMT-LIB `assert`
command.

The oracle rule can be used to introduce clauses that cannot be easily
explained.  It should be used as a last resort, if a full low-level
proof is too tedious, or if the axioms for the theory are missing.
The proof-checker allows any oracle clause but will warn about these
clauses.

The remaining rules are the low-level axioms of the proof format.
Each of them creates a tautological clause.  They are given in the
next section.

