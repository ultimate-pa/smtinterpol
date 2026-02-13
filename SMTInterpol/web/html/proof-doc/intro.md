# RESOLUTE – A Simple Proof Format for SMT-LIB

The SMT-LIB standard defines a command for requesting proofs from
solvers, but it does not prescribe how these proofs should be
represented. Different solvers therefore use different proof formats.

RESOLUTE is the proof format used by SMTInterpol. It is a low-level,
resolution-based format designed to be simple, explicit, and easy to
check. Proofs are represented as S-expressions and closely follow
SMT-LIB syntax wherever possible.

RESOLUTE proofs use the resolution rule to derive the empty clause
from the asserted formulas in the input and a fixed set of axioms for
logical and theory reasoning.  The format is intentionally minimal:
complex reasoning is reduced to resolution steps over explicitly
stated axioms.

We have a [proof checker](https://ultimate.informatik.uni-freiburg.de/smtinterpol/online/proof.html) for these proofs.

## Resolution proofs

A RESOLUTE proof is given as a tree of subproofs.  Each subproof
establishes the validity of a clause.  A *clause* is a set of
literals and semantically represents the disjunction of these literals.
A *literal* is a positive or negative atom and an *atom* is
a Boolean SMT-LIB term, in other words, an SMT-LIB formula.

We use `+ t` to denote the positive literal for the
term `t` and `- t` for the negative literal.  A clause is denoted by
an S-expression `( +/- t1 ... +/- tn )`.  As usual, a positive literal
represents the fact that the term is true, a negative literal that the
term is false, and a clause represents the fact that at least one of
its literals holds.

A resolution proof is a proof of the unsatisfiability of an SMT-LIB
input script.  It is given as a proof tree proving the empty clause,
where the internal nodes of the proof tree apply the resolution rule
and the leaves of the tree are the assumptions from the SMT-LIB input
script and logical or theory-specific axioms.

### Resolution Rule

The only inference rule in RESOLUTE is binary resolution.
If `proof1` proves a clause $C_1$ and `proof2` proves a clause $C_2$,
then the resolution with the pivot $t$ produces a proof of the clause
$(C_1\setminus \{+t\}) \cup (C_2\setminus\{-t\})$
where the complementary literals $+ t$ and $- t$ are removed from the
respective clauses.
The resolution step is written as `(res t proof1 proof2)`.
Clauses are treated as sets of literals; therefore, literals occurring in 
both $C_1$ and $C_2$ occur only once in the conclusion.
Strictly speaking, the resolution rule is sound even when the clauses $C_1$ and $C_2$ do not contain the pivot literal; however, the proof checker will issue
a warning in that case.

### Assumptions

Each input formula denoted by `(assert t)` in the SMT-LIB benchmark
can be used as an assumption in the proof.
The assumption is denoted by the S-expression `(assume t)`
and proves the unit clause `( + t )`.  Assumptions together with
axioms form the leaves of the proof tree.

### Axioms

In addition to assumptions, RESOLUTE uses a fixed collection of axioms
that encode the semantics of logical operators and background
theories.

Each axiom is represented as a clause that is universally valid.
These axioms serve as the basic building blocks from which all reasoning is derived.
An axiom is written as a proof term `(axiom-name parameter …)` that
proves a tautological clause.

In particular, the core theory defines the axioms for the logical
operators.  As an example, the axiom `(or+ 1 (or t0 t1 t2))` where
`t0`, `t1`, and `t2` are arbitrary terms is a proof for the valid
clause `( +(or t0 t1 t2) - t1 )`.

## Axioms for core theory

The meaning of logical operators is expressed by a set of core axioms
that are available in every SMT-LIB theory.  The axioms explicitly
support associative SMT-LIB operators like `and`, `or`, `=>` with more
than two arguments.

The following block is a schematic summary; the precise axioms are given
in "Core Axioms" below.  Axioms are written as `axiom-name: (clause)`.

```
; logical operators
true+: ( + true )                      false-: ( - false )
 not+: ( +(not p0) + p0 )                not-: ( -(not p0) - p0 )
 and+: ( +(and p0 … pn) - p0 … - pn )    and-: ( -(and p0 … pn) + pi )
  or+: ( +(or p0 … pn) - pi )             or-: ( -(or p0 … pn) + p0 … + pn )
  =>+: ( +(=> p0 … pn) +/- pi )           =>-: ( -(=> p0 … pn) - p0 … + pn )
  =+1: ( +(= p0 p1) + p0 + p1 )           =-1: ( -(= p0 p1) + p0 - p1 )
  =+2: ( +(= p0 p1) - p0 - p1 )           =-2: ( -(= p0 p1) - p0 + p1 )
 xor+: ( +(xor l1) +(xor l2) -(xor l3) ) xor-: ( -(xor l1) -(xor l2) -(xor l3) )
    where each term in l1,l2,l3 occurs an even number of times.

; quantifiers
  forall+: ( +(forall (x) (F x)) -(F (choose (x) (F x))) )
  forall-: ( -(forall (x) (F x)) +(F t) )
  exists+: ( +(exists (x) (F x)) -(F t) )
  exists-: ( -(exists (x) (F x)) +(F (choose (x) (F x))) )

; equality axioms
     refl: ( +(= t t) )                  symm: ( +(= t0 t1) -(= t1 t0) )
    trans: ( +(= t0 tn) -(= t0 t1) … -(= tn-1 tn) )
     cong: ( +(= (f t0 … tn) (f t'0 … t'n)) -(= t0 t'0) … -(= tn t'n) )
       =+: ( +(= t0 … tn) -(= t0 t1) … -(= tn-1 tn) )
       =-: ( -(= t0 … tn) +(= ti tj) )
distinct+: ( +(distinct t0 … tn) +(= t0 t1) … +(= t0 tn) … +(= tn-1 tn) )
distinct-: ( -(distinct t0 … tn) -(= ti tj) )   where i != j

; ite, define-fun, annotations
  ite1: ( +(= (ite t0 t1 t2) t1) - t0 )  ite2: ( +(= (ite t0 t1 t2) t2) + t0 )
  del!: ( +(= (! t :annotation…) t) )
expand: ( +(= (f t0 … tn) (let ((x0 t0)…(xn tn)) d)) )
   where f is defined by (define-fun f ((x0 τ0)…(xn τn)) τ d)
```

A detailed explanation of the axioms will be given in the section
"Core Axioms" below.

## Syntactic extensions

Conceptually a resolution proof is just a huge proof term applying the
resolution rule `res` to axioms and assumptions.  However, there are a few
important extensions to concisely express large proofs.

### let terms

A large proof may use the same large term multiple times.  These large
terms can be shared between different clauses in the proof.  To
express proofs in a concise manner, we support the `let` syntax from
SMT-LIB to bind terms to variables.  Such `let` terms
are seen as syntactic sugar and are equal to their expanded form,
i.e., no proof rule is required to expand a `let`.  In particular, the
resolution rule will also remove the pivot literal from the proved
clause if the pivot terms are only identical after let expansion.

To bind a proof to a variable, the `let-proof` keyword is used with
the same syntax as `let`.  This can be used to avoid repeating the
same subproof multiple times.  This proof variable may then be used
wherever a proof is expected, e.g., as arguments of the resolution
rule.

The `let-proof` syntax is also useful for expressing the proofs in a
linear form.  A solver may choose to print its proof incrementally
by binding each learned clause to a variable until the empty clause
is derived:

```
(let-proof ((C1 (assume …)))
(let-proof ((C2 (res … C1 …)))
…
 C100 ; empty clause
)…)
```

### Function definitions

The proof format also supports custom defined functions that are only
used inside the proof.  This is useful for auxiliary functions
that are created by Skolemization or by CNF conversion of quantified
formulas.  The syntax for this is `((define-fun f ((x0 τ0)…(xn τn)) d)
subproof)` where subproof may use the function symbol `f` and the
`cong` and `expand` axioms for this function symbol.

### Extended resolution

The proof calculus trivially supports extended resolution, where a fresh
atom `p` is introduced that represents `(and p0 p1)` and the three
clauses `( - p0 - p1 + p )`, `( - p + p0 )`, and `( - p + p1 )` are added.
This is facilitated by the `let` syntax and the axioms for logical
operators as follows:

```
(let ((p (and p0 p1)))
  (let-proof ((C1 (and+ p))
              (C2 (and- 0 p))
              (C3 (and- 1 p)))
    …))
```

Resolution proofs are usually only refutation complete, i.e., they can
prove the empty clause if the conjunction of the input clauses is
unsatisfiable.  However, the addition of the core axioms makes the
calculus complete in the sense that for every valid SMT-LIB formula `t`
there is a proof that proves the unit clause `( + t )`.

The proof calculus does not support RUP proofs directly.  They need to
be converted to applications of `res` by explicitly listing the
clauses and pivot term used in the unit propagation subproof.  More
importantly, DRAT proofs are not supported and there is no syntax for
deleting clauses.  Instead they need to be converted to extended
resolution (which blows up the proof quadratically).  On the other
hand, this simplifies the proof checker, which would otherwise
need to rediscover the necessary clauses and subproofs.

