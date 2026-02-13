## Equality between terms

A proof calculus needs to define which terms are intrinsically equal.
This equality relation needs to be decidable, but it should also
be simple for efficient implementation of proof checkers.  To ensure
consensus on when a proof is correct, we need to formally define this
intrinsic equality.

Equality is used by the proof checker in two places.  The first is for
the side condition of the `assume` rule, which requires that the assumed
term be equal to a formula asserted in the input problem.  The
second is for the set operations in the resolution rule, which remove
the pivot literal from the clauses
and eliminate duplicated elements in the resolvent.

In type theory, equality is usually defined by α-, β-, δ-, … reductions.  Here
we define our own reduction rules in the form of a rewrite system.  Two
terms are equal if they are rewritten to the same canonical term.

The rules are

```
x → t                where x in the current context is bound to t by a let
(let (...) t) → t    where t contains no variable bound by let
|symbol| → symbol    where symbol is a valid SMT-LIB symbol
numeral → numeral.0  only for LRA/NRA logics where numeral has sort Real
```

### Discussion

The above rules are minimal to keep the canonicalization of terms
simple.  The `let` rules are necessary for efficient proof
representation.  The `|symbol|` rule should help solvers whose internal
representation may not differentiate between quoted and unquoted terms.

The last rule for `numeral` is only used for matching the input
formula of the benchmark with the asserted formula in the proof.  It
is necessary because, when bitvectors are present, a proof is parsed as 
a term in the logic LIRA, since our bitvector rules use integers.
This means that every ⟨numeral⟩ in the input formula must be written as
the corresponding ⟨decimal⟩ in the proof.

Note that any change to these rules can make existing proofs invalid.
If new rules are added, this may cause resolution steps to become
superfluous and produce a warning that the pivot literal was not
found in the antecedent clause.  This could be solved by making the
resolution rule more lenient, but such a change would make debugging
faulty proofs much harder, since then only the final emptiness check for
the proved clause would fail.

### Clashing variable names

For the rewrite system above, variable names can clash. As an example,
consider the following term.

    (exists ((x Int)) (let ((y x)) (exists (x Int) (not (= x y)))))

When rewriting the above term using the let rules and replacing `y` by
its definition `x`, the proof validator needs to remember that `x` refers
to the variable bound by the outer quantifier and not to the inner one.
In particular, the above term is not equal (not even equivalent) to the term

    (exists ((x Int)) (exists (x Int) (not (= x x))))

Instead the term could be represented by

    (exists ((x₁ Int)) (exists (x₂ Int) (not (= x₂ x₁))))

