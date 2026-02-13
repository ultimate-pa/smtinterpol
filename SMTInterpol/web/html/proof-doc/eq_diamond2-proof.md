## Example Proof: eq-diamond2

We give an example proof of the following simple benchmark from the SMT-LIB benchmark library.

```smt2
(set-option :produce-proofs true)
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun x0 () U)
(declare-fun y0 () U)
(declare-fun z0 () U)
(declare-fun x1 () U)
(declare-fun y1 () U)
(declare-fun z1 () U)
(assert (and (or (and (= x0 y0) (= y0 x1)) (and (= x0 z0) (= z0 x1))) (not (= x0 x1))))
(check-sat)
(get-proof)
```

A valid output for this benchmark would be the following.

```smt2
unsat
(let ((t1 (= x0 y0))
      (t2 (= y0 x1))
      (t3 (= x0 z0))
      (t4 (= z0 x1))
      (t5 (= x0 x1)))
(let ((t6 (and t1 t2))
      (t7 (and t3 t4))
      (t8 (not t5)))
(let ((t9 (or t6 t7)))
(let ((t10 (and t9 t8)))
(let-proof ((C0 (assume t10)))
(let-proof ((C1 (res t9 (res t10 C0 (and- 0 t10)) (or- t9))))
(let-proof ((C2 (res t8 (res t10 C0 (and- 1 t10)) (not- t8))))
(let-proof ((C3 (and- 0 t6)))
(let-proof ((C4 (and- 1 t6)))
(let-proof ((C5 (and- 0 t7)))
(let-proof ((C6 (and- 1 t7)))
(let-proof ((C7 (res t5 (res t1 C3 (res t2 C4 (trans x0 y0 x1))) C2)))
    (res t5 (res t6 (res t7 C1 (res t4 C6 (res t3 C5 (trans x0 z0 x1)))) C7) C2)
))))))))))))
```

As mentioned earlier, the proof follows mostly the syntax of SMT-LIB terms.
In particular, it uses `let` and `let-proof` to bind terms and
subproofs to variables.  We now explain how such a proof can be constructed.

### Introducing names for subterms

The first ten lines define names for the subterms of the formula from
bottom-up.  Note that `t10` is the asserted formula in the input
file (after expanding `let` bindings).
It is not required to introduce an identifier for every subterm, but
doing so helps keep the proof small.

### CNF conversion

Then `C0` is defined, which is an input clause.  Using the `assume`
rule, an input clause can be proved as a unit clause.  As usual, a
clause is a list of literals, which are atoms with positive or
negative polarity.  In our proof calculus, the atoms are SMT-LIB terms
of type Boolean.  Thus, the input formula is represented by a unit clause
containing one positive atom that is the asserted term.

Every proof rule produces a proof of a clause.  The `assume` rule produces
the proof that the unit clause `( + t10 )` holds.  Clauses are written by
listing the literals in parentheses and the `+` indicates that the
literal has positive polarity.  This proof is then assigned
to the variable `C0` so it can be referenced in later proofs.

The next step is to convert the input formula into CNF.  We use
`C1`–`C7` for the clauses resulting from the conversion (or more
precisely, they are the proofs of the clauses of the CNF).  Let us
look at how this is done. The input formula `t10` is

    (and (or t6 t7) (not t5))

Thus, we want to split it into `C1: ( + t6 + t7 )` and `C2: ( - t5 )`.
To split the `and` formula, we use the `and-` elimination rule.  In this example
the axiom `(and- 0 t10)` is used to prove `t9` from `t10`.
Note that `t10` is just an abbreviation for `(and t9 t8)` and that `t9` is
the argument at index 0.
So the axiom `(and- 0 t10)` proves the tautology clause `( - t10 + t9 )`,
which states that `t10` implies `t9`.
By resolving this clause with the input formula `t10`, we get a proof of `t9`.  The resolution is written as `(res t10 C0 (and- 0 t10))`,
where `t10` is the pivot literal, `C0` is a proof of a clause containing it positively, and
`(and- 0 t10)` a proof containing it negatively.   The result is a proof
for `( + t9 )`.

The next step is to eliminate `(or t6 t7)`, that is `t9`, using the
`or-` elimination rule.  The axiom `(or- t9)` proves the tautology clause
`( - t9 + t6 + t7 )`.  Resolving it with the previous proof on the
pivot `t9`, we obtain `C1` which is a proof of `( + t6 + t7 )`.

    (let-proof ((C1 (res t9 (res t10 C0 (and- 0 t10)) (or- t9))))

Similarly we use the other `and-` elimination rule `(and- 1 t10)` and the `not-` elimination
rule `(not- t8)` to obtain from `C0` the clause `C2` that proves `( - t5 )`.

    (let-proof ((C2 (res t8 (res t10 C0 (and- 1 t10)) (not- t8))))

Furthermore, we add the clauses of the Plaisted–Greenbaum encoding
`C3`–`C6`.   These clauses are simply the `and-` elimination clauses, but this time applied to
`(and t1 t2)` and `(and t3 t4)`.  This gives us the full CNF of the input:

```
C1: ( + t6 + t7 )
C2: ( - t5 )
C3: ( - t6 + t1 )
C4: ( - t6 + t2 )
C5: ( - t7 + t3 )
C6: ( - t7 + t4 )
```

### SMT solving

The only unit clause `C2` propagates `- t5`.  We assume the
DPLL engine now decides the literal `+ t6` and propagates `+ t1` and
`+ t2` by unit propagation.  Then the theory solver finds the conflict
involving transitivity:

    (trans x0 y0 x1): ( - t1 - t2 + t5 )

By definition `t1` is `(= x0 y0)`, `t2` is `(= y0 x1)` and `t5` is
`(= x0 x1)`, so the transitivity axiom for `x0 = y0 = x1` has exactly
this form.

CDCL now explains the conflict, yielding `C7: ( - t6 )`

    (let-proof ((C7 (res t5 (res t2 C4 (res t1 C3 (trans x0 y0 x1))) C2)))

Now unit propagation derives `- t6`, `+ t7`, `+ t3`, and `+ t4`, and again
a theory conflict is found:

    (trans x0 z0 x1): ( - t3 - t4 + t5 )

The explanation of this conflict yields the empty clause:

    (res t5 (res t6 (res t7 C1 (res t4 C6 (res t3 C5 (trans x0 z0 x1)))) C7) C2)

This concludes the proof.
