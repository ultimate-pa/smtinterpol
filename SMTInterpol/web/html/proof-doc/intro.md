# RESOLUTE – A Simple Proof Format for SMT-LIB

Although the SMT-LIB format defines a command for obtaining proofs, it
does not prescribe the format for these proofs.  The only requirement
is that the result follows the grammar rule for s-expr.  This document
explains the proof format RESOLUTE, which is the lowlevel proof format
returned by the SMT solver SMTInterpol.

SMTInterpol internally can switch between different proof levels.  The
lowlevel proof format described in this document can be activated by
`(set-option :proof-level lowlevel)`.  The goal of the lowlevel proof
format is an easy to check format.  There are also the proof-levels
clauses (which adds all input clauses as oracles) and full, which uses
the internal proof rules using oracle clauses.

We have a [proof checker](https://ultimate.informatik.uni-freiburg.de/smtinterpol/online/proof.html) for these proofs.

## Resolution proofs

The proof is given as a resolution proof.  Each subproof proves the
validity of a clause where a clause is a set of literals and a
literal is a positive or negative atom.  An atom is an SMT-LIB term of
sort Bool, in other words, an SMT-LIB formula.  In particular input
formulas are seen as unit clauses with a single positive atom.  We
use `+ t` to denote the positive literal for the term `t` and `- t`
for the negative literal.  A clause is dentoed by an S-Expression
`( +/- t1 ... +/- tn)`.
As usual, a positive literal represents the fact that the term is
true, a negative literal that the term is false, and a clause
represents the fact that at least one of its literals hold.

A proof is build from the resolution rule, axioms, and assumptions.  A
proof is valid, if the side conditions for every axiom is fulfilled
and it proves the empty clause.  The main rule is the resolution rule:

$$\frac{C_1 \qquad C_2}{(C_1\setminus \{+ t\}) \cup (C_2\setminus\{- t\})}$$

The concrete syntax for the resolution rule is `(res t proof1 proof2)`
where `t` is the pivot atom (an SMT-LIB term), `proof1` a proof for a
clause $C_1$, and `proof2` a proof for a clause $C_2$.  The
proof `(res t proof1 proof2)` is then a proof for a new clause containing
all literals from
$C_1\setminus \{+ t\}$ and $C_2\setminus\{- t\}$
where $C\setminus\{\ell\}$ denotes the
clause $C$ with any occurrence of the literal $\ell$ removed.  A clause is
seen as a set of literals and literals appearing in both $C_1$ and $C_2$
appear only once in the conclusion.

Furthermore, there are several axioms for the different theories.  In
particular, the core theory defines the axioms for the logical
operators.  As an example, the axiom `(or+ 1 t0 t1 t2)` where
`t0`, `t1`, and `t2` are arbitrary terms is a proof for the valid
clause `(+(or t0 t1 t2) - t1)`.

Facts from the SMT-LIB script can be introduced using the syntax
`(assume term)`, which is a proof of the unit clause `(+ term)`
provided the SMT-LIB script contains the assertion `(assert term)`.  A
proof of the unsatisfiability of an SMT-LIB input script is a proof of
the empty clause that only uses the assumptions appearing in the
SMT-LIB script.

## Axioms for core theory

The meaning of logical operators is expressed by a set of core axioms
that are available in every SMT-LIB theory.  The axioms explicitly
support associative SMT-LIB operators like `and`, `or`, `=>` with more
than two arguments.

```
; axioms are written as name-of-axiom: (clause)
; logical operators
true+: (+ true)                      false-: (- false)
 not+: (+(not p0) + p0)                not-: (-(not p0 ) - p0)
 and+: (+(and p0 … pn) - p0 … - pn)    and-: (-(and p0 … pn) + pi)
  or+: (+(or p0 … pn) - pi )            or-: (-(or p0 … pn) + p0 … + pn)
  =>+: (+(=> p0 … pn) +/- pi )          =>-: (-(=> p0 … pn) - p0 … + pn)
  =+1: (+(= p0 p1) + p0 + p1)           =-1: (-(= p0 p1) + p0 - p1)
  =+2: (+(= p0 p1) - p0 - p1)           =-2: (-(= p0 p1) - p0 + p1)
 xor+: (+(xor l1) +(xor l2) -(xor l3)) xor-: (-(xor l1) -(xor l2) -xor(l3))
    where each term in l1,l2,l3 occurs an even number of times.

; quantifiers
forall+: (+(forall x (F x)) -(F (choose x (F x))))
forall-: (-(forall x (F x)) +(F t))
exists+: (+(exists x (F x)) -(F t))
exists-: (-(exists x (F x)) +(F (choose x (F x))))

; equality axioms
     refl: (+(= t t))                    symm: (+(= t0 t1) -(= t1 t0))
    trans: (+(= t0 tn) -(= t0 t1) … -(= tn-1 tn))
     cong: (+(= (f t0 … tn) (f t0' … tn')) -(= t0 t0') … -(= tn tn'))
       =+: (+(= t0 … tn) -(= t0 t1) … -(= tn-1 tn))
       =-: (-(= t0 … tn) +(= ti tj))
distinct+: (+(distinct t0 … tn) +(= t0 t1) … +(= t0 tn) … +(= tn-1 tn))
distinct-: (-(distinct t0 … tn) -(= ti tj))   where i != j

; ite, define-fun, annotations
  ite1: (+(= (ite t0 t1 t2) t1) - t0)   ite2: (+(= (ite t0 t1 t2) t2) + t0)
  del!: (+(= (! t :annotation…) t))
expand: (+(= (f t0 … tn) (let ((x0 t0)…(xn tn)) d)))
   where f is defined by (define-fun f ((x0 τ0)…(xn τn)) τ d)
```

A detailed explanation of the axioms will be given in the section
Core Axioms below.

## Syntactic extensions

Conceptually a resolution proof is just a big proof term applying the
resolution rule `res` to axioms and assumptions.  However, there are a few
important extensions to concisely express large proof.

### let-terms

A large proof may use the same large term multiple times.  These large
terms can be shared between different clauses in the proof.  To
express proofs in a concise manner, we support the `let` syntax from
SMT-LIB to bind terms to variables.  Such `let` terms
are seen as syntactic sugar and are equal to their expanded form,
i.e., no proof rule is required to expand a `let`.  In particular, the
resolution rule will also remove the pivot literal from the proved
sub-clause if they are only identical after let expansion.

To bind a proof to a variable, the `let-proof` keyword is used with
the same syntax as `let`.  This can be used to avoid repeating the
same subproof multiple times.  This proof variable may then be used
whereever a proof is expected, e.g., as arguments of the resolution
rule.

The `let-proof` syntax is also useful for expressing the proofs in a
linear form.  A solver may choose to print its proof on the fly by
printing each learned clause and binding it to a variable until it
derives the empty clause:

```
(let-proof ((C1 (assume …)))
(let-proof ((C2 (res … C1 …)))
…
 C100 ; empty clause
)…)
```

### Function definitions

The proof format also supports custom defined functions that are only
used inside the proof.  This can be usefule for auxiliary functions
that are created by Skolemization or by CNF conversion of quantified
formulas.  The syntax for this is `((define-fun f ((x0 τ0)…(xn τn)) d)
subproof)` where subproof may use the function symbol `f` and the
`cong` and `expand` axioms for this function symbol.

### Extended resolution

The proof calculus trivially supports extended resolution, where a new
literal `p` is introduced that represents `(and p0 p1)` and the three
clauses `(- p0 - p1 + p)`, `(- p + p0)`, and `(- p + p1)` are added.
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
prove the empty clause if the conjunction of the input clauses are
unsatisfiable.  However, the addition of the core axioms makes the
calculus complete in the sense that for every valid SMT-LIB formula `t`
there is a proof that proves the unit clause `(+ t)`.

The proof calculus does not support RUP proofs directly.  They need to
be converted to applications of `res` by explicitly listing the
clauses and pivot term used in the unit propagation subproof.  More
importantly DRAT proofs are not supported and there is no syntax for
deleting clauses.  Instead they need to be converted to extended
resolution (which blows up the proof quadratically).  On the other
hand, this simplifies the proof checker, which would otherwise
need to rediscover the necessary clauses and subproofs.

