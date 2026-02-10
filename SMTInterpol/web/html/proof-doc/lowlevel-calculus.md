## Core Axioms

The core axioms are ⟨proof⟩ objects that prove a tautological clauses.
Their inputs are usually ⟨term⟩s.  We distinguish the following
categories.

### Logical axioms – elimination and introduction

For every logical operator we have the usual elimination and
introduction rules.  In our calculus they take the form of a clause
where the premises have negative polarity and the conclusion has
positive polarity.  They are also identical to the clauses that
Tseitin-encoding gives.  The following list the axioms and the
corresponding clause proved by this axiom.  In this list `t, t0,…`
denote terms, `n,i,j` denote numerals.  The elimination rules are
indicated by `-` and the introduction rules are indicated by `+`.

```
⟨core-axiom⟩ ::=
 | (false-)               ;( - false )
 | (true+)                ;( + true )
 | (not+ (not t))         ;( +(not t) + t )
 | (not- (not t))         ;( -(not t) - t )
 | (and+ (and t0 … tn))   ;( +(and t0 … tn) - t0 … - tn)
 | (and- i (and t0 … tn)) ;( -(and t0 … tn) + ti)
 | (or+ i (or t0 … tn))   ;( +(or t0 … tn) - ti)
 | (or- (or t0 … tn))     ;( -(or t0 … tn) + t0 … + tn)
 | (=>+ (=> i t0 … tn))   ;( +(=> t0 … tn) + ti)        (for i < n)
 | (=>+ n (=> t0 … tn))   ;( +(=> t0 … tn) - tn)
 | (=>- (=> t0 … tn))     ;( -(=> t0 … tn) - t0 … - tn-1 + tn)
 | (=+1 (= t0 t1))        ;( +(= t0 t1) + t0 + t1)      (only for Boolean t0/t1)
 | (=+2 (= t0 t1))        ;( +(= t0 t1) - t0 - t1)      (only for Boolean t0/t1)
 | (=-1 (= t0 t1))        ;( -(= t0 t1) + t0 - t1)      (only for Boolean t0/t1)
 | (=-2 (= t0 t1))        ;( -(= t0 t1) - t0 + t1)      (only for Boolean t0/t1)
 | …                      ;;; see next section
```

All rules containing `i` have the implicit constraint `0 <= i <= n`.

### Equality rules

We support the usual axioms of reflexivity, symmetry, transitivity
(with arbitrarily long chains), and congruence:

```
⟨core-axiom⟩ ::= …
 | (refl t):              ;( +(= t t) )
 | (symm t0 t2):          ;( +(= t0 t1) -(= t1 t0) )
 | (trans t0 … tn):       ;( +(= t0 tn) -(= t0 t1) … -(= tn-1 tn) )  (for n >= 2)
 | (cong (f t0 … tn) (f t'0 … t'n))
                       ;( +(= (f t0 … tn) (f t'0 … t'n))
                       ;  -(= t0 t'0) … -(= tn t'n))
```

Additionally we have elimination and introduction rules for equality chains and
for distinct:

```
⟨core-axiom⟩ ::= …
 | (=+ (= t0 … tn)):              ;( +(= t0 … tn) -(= t0 t1) … -(= tn-1 tn))
 | (=- i j (= t0 … tn)):          ;( -(= t0 … tn) +(= ti tj))
 | (distinct+ (distinct t0 … tn)) ;( +(distinct t0 … tn)
                                  ;  +(= t0 t1) … +(= t0 tn)
                                  ;  +(= t1 t2) … +(= t2 tn)…
                                  ;  +(= tn-1 tn))
 | (distinct- i j (distinct t0 … tn)); ( -(distinct t0 … tn) -(= ti tj))      (for i != j)
```

The rules containing `i,j` have the implicit constraint `0 <= i <= n`, `0 <= j <= n`.
For `=` we have n >= 2. for `distinct` we have `n >= 1`.

### ite rules

To support ite terms, we have two simple axioms (`t0` is the condition).

```
⟨core-axiom⟩ ::= …
 | (ite1 (ite t0 t1 t2))   ;( - t0 +(= (ite t0 t1 t2) t1) )
 | (ite2 (ite t0 t1 t2))   ;( + t0 +(= (ite t0 t1 t2) t2) )
```

### xor rules

For efficient `xor` reasoning we allow arbitrary split and reordering
of the xor arguments between three xor terms.  The rules are

```
⟨core-axiom⟩ ::= …
 | (xor+ (t̅0) (t̅1) (t̅2)   ;( +(xor t̅0) +(xor t̅1) -(xor t̅2) )
 | (xor- (t̅0) (t̅1) (t̅2)   ;( -(xor t̅0) -(xor t̅1) -(xor t̅2) )
```

where `t̅0,t̅1,t̅2` are three non-empty sequences of terms that in total
contain every term an even number of times.  Furthermore, if one of
the sequences `t̅i` consists of only a single term `ti` then the clause
contains the atom `ti` instead of the corresponding xor-term.  For
example:

```
(xor+ (t0 t1 t2) (t1) (t2 t0)): ( +(xor t0 t1 t2) + t1 -(xor t2 t0) )
(xor- (t t) (t t) (t t)):       ( -(xor t t) )
```

Note that the last rule uses the fact that a clause is a set of literals,
so multiple occurrences of literals are implicitly removed.

### Quantifier instantiation and Skolemization

The rules for quantifier introduction and elimination bind the
quantified variables either by an arbitrary term or use the
choose operator (the Hilbert epsilon operator).

```
⟨core-axiom⟩ ::= …
 | (forall+ (forall ((x0 X0) … (xn Xn)) F))
    ;( +(forall ((x0 X0) … (xn Xn)) F)
    ;  -(let ((x0 (choose (x0 X0) (not (forall ((x1… xn Xn)) F)))))
    ;    (let ((x1 (choose (x1 X1) (not (forall ((x2… xn Xn)) F)))))
    ;     …
    ;     (let ((xn (choose (xn X)) (not F))) F)..)) )
 | (forall- (t0 … tn) (forall ((x0 X0) … (xn Xn)) F)):
    ;( -(forall ((x0 X0) … (xn Xn)) F) +(let ((x0 t0) … (xn tn)) F) )
 | (exists+ (t0 … tn) (exists ((x0 X0) … (xn Xn)) F)):
    ;( +(exists ((x0 X0) … (xn Xn)) F) -(let ((x0 t0) … (xn tn)) F) )
 | (exists- (exists ((x0 X0) … (xn Xn)) F))
    ;( -(exists ((x0 X0) … (xn Xn)) F)
    ;  +(let ((x0 (choose (x0 X0) (exists ((x1… xn Xn)) F))))
    ;    (let ((x1 (choose (x1 X1) (exists ((x2… xn Xn)) F))))
    ;     …
    ;      (let ((xn (choose (xn X)) F)) F)…)) )
```

In forall- and exists+, `Xi` is the type of `ti`.

### Miscellaneous rules

For every symbol defined by `define-fun` we have a rule that expands the
function definition.  Assume `f` is defined as

    (define-fun f ((x0 X0) … (xn Xn)) X t)

then the expand rule for `f` is

```
⟨core-axiom⟩ ::= …
 | (expand (f t0 … tn)) ;( +(= (f t0 … tn) (let ((x0 t0) … (xn tn)) t)))
```

Note that the `:named` attribute is implicitly expanded to define-fun
according to the standard and therefore the expand rule can also be
used for named terms.

Proofs can also contain `define-fun` with the same syntax.  These will
define the function symbol for the subproof and enable the `expand`
rule there.  The defined function symbol must not be used outside the
subproof.  The `declare-fun` will add the function, but will not allow
any `expand` of this function, only congruence is allowed.

There is also a `refine-fun` which adds a function definition to an
already declared function.  It is only allowed on the outermost layer
of satisfiability proofs and is used to fix the model for
uninterpreted function occuring in the benchmark.

For some internal functions, the expand rule is also applicable.
For every function with the LEFTASSOC, RIGHTASSOC, CHAINABLE, or
PAIRWISE attribute and more than two arguments expand will apply
the transformation given by the SMT-LIB standard, e.g.:

```
(expand (or t0 … tn)): ( +(= (or t0 … tn)
                              (or … (or t0 t1) … tn)))
(expand (=> t0 … tn)): ( +(= (=> t0 … tn)
                              (or t0 … (or tn-1 tn) … )))
(expand (< t0 … tn)):  ( +(= (< t0 … tn)
                              (and (< t0 t1) … (tn-1 tn))))
```

Theories have their own expand rules for some of the theory functions,
like `abs` or `(_ divisible k`.  These are listed in the section
describing the theory extensions.

We also have a simple rule to delete attributes from input terms

```
⟨core-axiom⟩ ::= …
 | (del! t :attributes…)  ;( +(= (! t :attributes…) t) )
```

