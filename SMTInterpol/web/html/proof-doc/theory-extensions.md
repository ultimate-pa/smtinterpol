## Extensions for other theories

When adding more theories, we need to add more axioms to support
these theories.  Here we list the axioms for the theories that
SMTInterpol supports.

### Array Theory

We add the McCarthy axioms and an axiom for extensionality.  We choose
the axiom with an explicit `@diff` operator that returns an index witnessing
a difference between two arrays.

```
⟨array-axiom⟩ ::=
 | (selectstore1 a i v)   ;( +(= (select (store a i v) i) v) )
 | (selectstore2 a i j v) ;( +(= (select (store a i v) j) (select a j)) +(= i j) )
 | (extdiff a b)          ;( +(= a b) -(= (select a (@diff a b)) (select b (@diff a b))) )
```

To support const arrays, one additional axiom is needed:

```
 | (const v i)            ;( +(= (select (@const v) i) v) )
```

### Arithmetic

For arithmetic we need to manipulate polynomials.  Polynomials are
represented by an SMT-LIB term of the following form.

```
  (+ (* c1 t11 … t1m) … (* cn tn1 … tnm))
```

Here `c1`, …, `cn` are constants (⟨numeral⟩, ⟨decimal⟩, or integer/real
numbers in canonical form).  All `(ti1 … tim)` are different multisets, and
the head symbol of `tij` is not `+` or `*`.  All `ci`, `tij` have the same type
(`Real` or `Int`).  The constant `ci` may be omitted if it is `1`,
except if there are no other terms in the monomial.
The operators `*` and `+` are omitted
if they have only one argument. The zero polynomial is represented by `0`.

When multiplying polynomials or adding them together, the usual rules of
distributivity, commutativity, and associativity are applied to bring them
into the above normal form again.

We have four rules that manipulate these polynomials.  The first two
perform polynomial addition and multiplication:

```
⟨arith-axiom⟩ ::=
 | (poly+ (+ a1 … an) a):  ;( +(= (+ a1 … an) a) )  where a1+…+an = a
 | (poly* (* a1 … an) a):  ;( +(= (* a1 … an) a) )  where a1*…*an = a
 | …
```

Here `a1`, …, `an`, `a` are polynomials.  The side-condition
`a1+…+an=a` states that adding the polynomial `a1`, …,
`an` yields a polynomial equal to `a`, i.e., it has the same
monomials with the same coefficients, but may differ in term order.
Similarly for `a1*…*an=a`.

Then we have one rule for `to_real`:

```
⟨arith-axiom⟩ ::= …
 | (to_real-def a)  ;( +(= (to_real a) a') )
```

where `a` is a polynomial `(+ … (* ci … tij …))` with integer coefficients and terms
and `a'` is the polynomial `(+ … (* ci' … (to_real tij) …))`
where `ci'` is the real representation of the integer `ci`, i.e.,
an integer `NUM` is replaced with `NUM.0`
and `(- NUM)` is replaced with `(- NUM.0)`.  Every other term `t` is replaced
by `(to_real t)`.

The heart of the proof system is the following rule proving the
inconsistency of a set of inequalities by using Farkas' Lemma.
(Note that this is only complete for linear arithmetic).

```
⟨arith-axiom⟩ ::= …
 | (farkas c1 (<=? a1 b1) … cn (<=? an bn)): ( -(<=? a1 b1) … -(<=? an bn) )
```

where `ci` are positive integers, `<=?` stands for `<`, `<=`, or `=`,
`ai`, `bi` are polynomials.  The weighted sum of these polynomials,
`c1*(a1-b1) + … + cn*(an-bn)` is a (rational or integer) constant `c`
where `c >= 0`.  If `c = 0`, then at least one inequality must be strict.
If some inequalities are over `Int` and some are over `Real`, all inequalities are
implicitly converted to `Real` by converting all coefficients in `ai`/`bi` to
real constants and replacing all terms `t` in `ai`/`bi` with `(to_real t)`.

For multiplicative reasoning, we provide a similar axiom stating that
the product of non-negative values is non-negative, and that the result is
strictly positive if all factors are strictly positive.

```
⟨arith-axiom⟩ ::= …
 | (mulpos (<=? 0 a1) … (<=? 0 an) (<=? 0 a)): ( -(<=? 0 a1) … -(<=? 0 an) +(<=? 0 a) )
```

where `<=?` stands for `<` or `<=`, `ai` are polynomials, and
`a = a1 * … * an` is the product of the polynomials `a1`, …, `an`.
The conclusion must be non-strict, i.e., `(<= 0 a)`, unless all
premises are strict inequalities `(< 0 ai)`, in which case the conclusion
may also be strict.

The remaining axioms work with arbitrary terms and do not require adding
or multiplying polynomials:

```
⟨arith-axiom⟩ ::= …
 | (trichotomy a b)   ;( +(< a b) +(= a b) +(< b a) )
 | (total a b)        ;( +(<= a b) +(< b a) )
```

The only side condition is that the terms in the clause type check.
For integer reasoning we use the following axiom that states that
there is no number between `c` and `c+1`:

```
⟨arith-axiom⟩ ::= …
 | (total-int a c)    ;( +(<= a c) +(<= (c+1) a) )
```

where `c` is an integer constant (NUMERAL or negated NUMERAL) and `(c+1)`
is the SMT-LIB representation of that constant plus one.  The term `a` is
an arbitrary term of sort `Int`.  Note: an alternative would be to
restrict the axiom to `c = 0`; i.e., `(total-int a)` proves `( +(<= a 0) +(<= 1 a) )`

Also we need the following axioms for handling division and modulo.
The rules are for the theories that contain the corresponding function
symbols.  Note that these rules are syntactic.  No polynomial
normalization is performed in these rules.

```
⟨arith-axiom⟩ ::= …
 | (/def a b1 … bn)  ;( +(= a (* b1 … bn (/ a b1 … bn))) +(= b1 0) … +(= bn 0) )
 | (div-low x d):    ;( +(<= (* d (div x d)) x) +(= d 0) )
 | (div-high x d):   ;( +(< x (+ (* d (div x d)) (abs d))) +(= d 0) )
 | (mod-def x d):    ;( +(= (mod x d) (- x (* d (div x d)))) +(= d 0) )
 | (to_int-low x):   ;( +(<= (to_real (to_int x)) x) )
 | (to_int-high x):  ;( +(< x (+ (to_real (to_int x)) 1.0)) )
```

In addition to the axioms above, we also add new definitions for the
`expand` axioms.   These are given in the following table:

```
(define-fun - ((x Int)) Int (* (- 1) x))
(define-fun - ((x Real)) Real (* (- 1) x))
(define-fun - ((x Int) (y Int)) Int (+ x (* (- 1) y)))
(define-fun - ((x Real) (y Real)) Real (+ x (* (- 1.0) y)))
(define-fun > ((x Int) (y Int)) Bool (< y x))
(define-fun > ((x Real) (y Real)) Bool (< y x))
(define-fun >= ((x Int) (y Int)) Bool (<= y x))
(define-fun >= ((x Real) (y Real)) Bool (<= y x))
(define-fun abs ((x Int)) Int (ite (< x 0) (- x) x))
(define-fun abs ((x Real)) Real (ite (< x 0) (- x) x))
(define-fun (_ divisible c) ((x Int)) Bool (= x (* c (div x c))))
(define-fun is_int ((x Real)) Bool (= x (to_real (to_int x))))
```

The other proof rules do not use the symbols `-`, `/`, `>=`, `>`.  A solver
should first rewrite them using these definitions and then only
work with `<=`, `<`, `*`, `+`.
Note that in `(divisible-def c x)` the constant `c` must be a positive
numeral larger than zero, to make the term `((_ divisible c) x)`
syntactically correct.

Also for every internal binary function in LIRA that takes two
reals, we define corresponding functions that take a mix of `Int`
and `Real` arguments and cast all integer arguments to `Real`.
This is supported by the `expand` rule and works even if
the function is used with more than two arguments.
As an example, for `(+ i0 r1 i2 r3)` where `i0`, `i2` are terms of
sort `Int` and `r1`, `r3` are terms of sort `Real`, the `expand`
axiom looks like:

```
(expand (+ i0 r1 i2 r3)): ( +(= (+ i0 r1 i2 r3)
                                (+ (to_real i0) r1 (to_real i2) r3)))
```

For algebraic completeness of the real numbers we need a generic representation
of algebraic numbers.  We use `(root-of (coeffs m0 ... mn) L R)` to represent
a root of the uni-variate polynomial with the coefficients `m0`,..., `mn`, provided
the sign of the polynomial differ at `L` and `R` or it evaluates to zero at L or R.
The sign condition ensures that the root is existing.
If `L <= R`, then the value returned by `root-of` is in the closed interval `[L,R]` (if
the sign condition does not hold, `root-of` returns an arbitrary value in the interval).
If `m(L)` or `m(R)` is zero, then the value returned by `root-of` can be `L` or `R`.
The terms `m0`, ..., `mn`, `L`, `R` can be any arbitrary SMT-LIB terms.
For example, if `p` and `q` are uninterpreted constants of type `Real`, the term

```
(let ((D (+ (* p p) (* (- 4.0) q)
  (root-of (coeffs q p 1.0)
    (+ (* (/ 1.0 2.0) D) (* (/ (- 1.0) 2.0) p))
    (+ (/ 1.0 2.0) (* (/ (- 1.0) 2.0) p))))
```

represents a root of the polynomial `x^2 + px + q` if `D >=0` (which ensures the sign condition).
The root lies in the interval `[D/2-b/2, 1/2-b/2]` for `D <= 1`.
For reasoning about `root-of` we use the following axioms:

```
⟨arith-axiom⟩ ::= …
 | (root-of-low m L R)    ;( -(<= L R) +(<= L (root-of m L R)) )
 | (root-of-high m L R)   ;( -(<= L R) +(<= (root-of m L R) R) )
 | (root-of-exists1 m L R (peval m L) (peval m R) (peval m (root-of m L R)))
  ; where (peval m t) is some normalization of the polynomial `(+ m0 (* t (+ m1 ... (* t mn)....)))`
  ;( -(<= (peval m L) 0.0) -(<= 0.0 (peval m R)) +(= (peval m (root-of m L R)) 0.0) )
 | (root-of-exists2 m L R (peval m L) (peval m R) (peval m (root-of m L R)))
  ; where (peval m t) is some normalization of the polynomial `(+ m0 (* t (+ m1 ... (* t mn)....)))`
  ;( -(<= 0.0 (peval m L)) -(<= (peval m R) 0.0) +(= (peval m (root-of m L R)) 0.0) )
```

As in the axioms `mulPos`, the terms `(peval m t)` must be provided as arguments because the
normalization of polynomials is only unique modulo the order of the monomials and factors
inside each monomial.
The axioms `root-of-low/root-of-high` ensure that the value is always within the closed interval.
We do not require that `L <= R`, for `(root-of-exists1/2)`, because the axiom is sound without it.

If you want to show `(=> (<= (* 4.0 q) (* p p)) (exists ((x Real)) (+ (* x x) (* p x) q)))`, you can
use the `root-of` term from the example above as a witness for the existential quantifier.  The
proof still requires a case distinction on `(<= 0.0 D)` and `(<= D 1.0)` because the sign of
`(peval m L)` and `(peval m R)` flip at `D = 1` and the other `root-of-exists` axiom is needed.

Note that the axiom `farkas` and `mulpos` are the only axioms that introduce negated literals.
The axiom `farkas` also supports equalities but treats them in the same way as inequalites `<=`.
If the opposite direction is required, symmetry must be applied first.

The `farkas` axiom can be used in a resolution proof to rewrite a positive equality or inequality
into a negated inequality.
Conversely, the axioms `total` and `total-int` can be used to rewrite a negated literal
into an equivalent positive literal.
The combination of these axioms allows one to derive a positive inequality from an equality.
For example, the following proof term derives a clause expressing that `(= a b)` implies `(<= a b)`:

```
(res (< b a)
     (total a b)
     (farkas 1 (= a b) 1 (< b a)))
```

### Data Types

For reasoning about data types, the following rules are used:

```
⟨datatype-axiom⟩ ::= …
 | (dt_project seli a1 … an)       ;( +(= (seli (cons a1 … an)) ai) )
 | (dt_cons cons x)                ;( -((_ is cons) x) +(= (cons (sel1 x) … (seln x)) x) )
 | (dt_test cons (cons a1 … an))   ;( +((_ is cons) (cons a1 … an)) )
 | (dt_test cons' (cons a1 … an))  ;( -((_ is cons') (cons a1 … an)) )
 | (dt_exhaust x)                  ;( +((_ is cons1) x) … +((_ is consn) x) )
 | (dt_acyclic t0 (i1 … in))       ;( -(= t0 tn) )
   ; where t0 is a nested constructor application and tn a subterm of t0 on the path (i1 … in), i.e.,
   ; for the sequence t0, …, tn (n >= 1), each tj is the ij-th argument of tj-1 for j = 1, …, n,
   ; t0, …, tn-1 are applications of constructors (not necessarily the same constructor or data type).
 | (dt_match (match t …))
   ;( +(= (match t ((p1 x1) c1) …) (ite ((_ is p1) t) (let ((x1 (sel1 t))) c1) …)) )
```

### Bitvectors

The idea is to translate bitvectors into integer arithmetic.  We
use the new functions `ubv_to_int` and `int_to_bv` introduced in
SMT-LIB version 2.7 to convert between integers and bitvectors.

We have the following correspondences:

```
⟨bitvector-axiom⟩ ::=
 | (int2ubv2int k t0)  ;( +(= (ubv_to_int ((_ int_to_bv k) t0)) (mod t0 2^k)) )
 | (int2sbv2int k t0)  ;( +(= (sbv_to_int ((_ int_to_bv k) t0)) (+ (mod (+ t0 2^(k-1)) 2^k) (- 2^(k-1)))) )
 | (ubv2int2bv t0)     ;( +(= ((_ int_to_bv k) (ubv_to_int t0)) t0) )
                       ; where t0 is of sort (_ BitVec k)
```

In these axioms `2^k`, `2^(k-1)` stand for the corresponding numerals,
e.g., for $k=3$ the axiom `(int2sbv2int 3 t0)` proves the clause
`( +(= (sbv_to_int ((_ int_to_bv 3) t0)) (+ (mod (+ t0 4) 8) (- 4))))`.
The axiom is syntactic, i.e., the term `(+ t0 4)` is not simplified if `t0` is
an arithmetic term.
In `(ubv2int2bv t0)` the width `k` is implicitly determined by the sort
of `t0`, which is `(_ BitVec k)`.  This is not possible for the other
two axioms because `t0` has sort `Int`.

The following definitions handle arithmetic:

```
(define-fun bvadd ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (+ (ubv_to_int x) (ubv_to_int y))))
(define-fun bvsub ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (+ (ubv_to_int x) (* (- 1) (ubv_to_int y)))))
(define-fun bvneg ((x (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (* (- 1) (ubv_to_int x))))
(define-fun bvmul ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (* (ubv_to_int x) (ubv_to_int y))))
(define-fun bvudiv ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (ite (= (ubv_to_int y) 0) (- 1) (div (ubv_to_int x) (ubv_to_int y)))))
(define-fun bvurem ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   (ite (= (ubv_to_int y) 0) x ((_ int_to_bv k) (mod (ubv_to_int x) (ubv_to_int y)))))
(define-fun bvsdiv ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   (let ((ix (sbv_to_int x)) (iy (sbv_to_int y)))
   ((_ int_to_bv k) (ite (< ix 0)
            (ite (< iy 0) (div (* (- 1) ix) (* (- 1) iy)) (ite (= iy 0) 1 (* (- 1) (div (* (- 1) ix) iy))))
            (ite (< iy 0) (* (- 1) (div ix (* (- 1) iy))) (ite (= iy 0) (- 1) (div ix iy)))))))
(define-fun bvsrem ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   (let ((ix (sbv_to_int x)) (iy (sbv_to_int y)))
   ((_ int_to_bv k) (ite (= iy 0) ix
            (ite (< ix 0) (* (- 1) (mod (* (- 1) ix) iy)) (mod ix iy))))))
(define-fun bvsmod ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   (let ((ix (sbv_to_int x)) (iy (sbv_to_int y)))
   ((_ int_to_bv k) (ite (= iy 0) ix (ite (< iy 0) (+ (mod (+ ix (- 1)) iy) iy 1) (mod ix iy)))))
(define-fun bvnego ((x (_ BitVec k))) Bool
   (= (sbv_to_int x) (- 2^(k-1))))
(define-fun bvuaddo ((x (_ BitVec k)) (y (_ BitVec k))) Bool
   (<= 2^k (+ (ubv_to_int x) (ubv_to_int y))))
(define-fun bvumulo ((x (_ BitVec k)) (y (_ BitVec k))) Bool
   (<= 2^k (* (ubv_to_int x) (ubv_to_int y))))
(define-fun bvusubo ((x (_ BitVec k)) (y (_ BitVec k))) Bool
   (< (ubv_to_int x) (ubv_to_int y)))
(define-fun bvsaddo ((x (_ BitVec k)) (y (_ BitVec k))) Bool
   (let ((sum (+ (sbv_to_int x) (sbv_to_int y))))
     (or (< sum (- 2^(k-1))) (<= 2^(k-1) sum)))
(define-fun bvsmulo ((x (_ BitVec k)) (y (_ BitVec k))) Bool
   (let ((prod (* (sbv_to_int x) (sbv_to_int y))))
     (or (< prod (- 2^(k-1))) (<= 2^(k-1) prod)))
(define-fun bvsdivo ((x (_ BitVec k)) (y (_ BitVec k))) Bool
   (and (= (sbv_to_int x) (- 2^(k-1))) (= (sbv_to_int y) (- 1))))
(define-fun bvssubo ((x (_ BitVec k)) (y (_ BitVec k))) Bool
   (let ((diff (+ (sbv_to_int x) (* (- 1) (sbv_to_int y)))))
     (or (< diff (- 2^(k-1))) (<= 2^(k-1) diff)))
```

Again, `2^(k-1)` and `2^k` stand for the corresponding numerals
where `k` is the length of the bitvector.

We use `(* (- 1) x)` instead of `(- x)` to avoid another expansion of `-`.
Note that the sign of `bvsrem` always matches the sign of the dividend and the sign of `bvsmod` always
matches the sign of the divisor. The rounding behavior of `bvsdiv` is towards zero and corresponds
to the modulo computed by `bvsrem`. This contrasts to integer `div` and `mod`, where `mod` is always
non-negative and `div` rounds to negative infinity for positive divisor and to positive infinity for
negative divisor.


For shifts, we define a function `pow2` for shifts and its inverse `log2`. We add a few axioms.

```
⟨bitvector-axiom⟩ ::= …
 | (pow2const k) ;( +(= (pow2 k) 2^k) )    ; where k >= 0 is a constant
 | (pow2add n m) ;( -(<= 0 n) -(<= 0 m) +(= (pow2 (+ n m)) (* (pow2 n) (pow2 m))) )
 | (log2low a)   ;( -(<= 0 a) +(<= (pow2 (log2 a)) a) )
 | (log2high a)  ;( -(<= 0 a) +(< a (* 2 (pow2 (log2 a)))) )
```

```
(define-fun bvshl ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (* (pow2 (ubv_to_int y)) (ubv_to_int x))))
(define-fun bvlshr ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (div (ubv_to_int x) (pow2 (ubv_to_int y)))))
(define-fun bvashr ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (div (sbv_to_int x) (pow2 (ubv_to_int y)))))
```

For logical operations we use a `&` operator over integers
that computes bitwise AND.
It is left-associative, takes two integers, and returns an integer.
It returns a negative number if and only if both arguments
are negative and ensures that no bits are truncated before performing
bitwise AND.

```
⟨bitvector-axiom⟩ ::= …
 | (&flat (& (& a_ij)) (& bi))
      ;( +(= (& (& a_11 …) … (& an1 …)) (& b_1 … b_m)) ) where {b_i} ∪ {-1} = { a_ij }
      ;     ( if an "&" has only one parameter, the & is omitted)
 | (&shift a b k)      ;( -(<= 0 k) +(= (* (& (div a (pow2 k)) b) (pow2 k)) (& a (* b (pow2 k)))) )
 | (&split a b)        ;( +(= (+ (& a b) (& a (+ (* (- 1) b) (- 1)))) a) )
 | (&bound a b)        ;( -(<= 0 a) +(<= (& a b) a) )
 | (&nonneg a b)       ;( -(<= 0 a) +(<= 0 (& a b)) )
```

Using this function we can define the logical operators:

```
(define-fun bvnot ((x (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (+ (- 1) (* (- 1) (ubv_to_int x)))))
(define-fun bvand ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (& (ubv_to_int x) (ubv_to_int y))))
(define-fun bvor ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (+ (ubv_to_int x) (ubv_to_int y) (* (- 1) (& (ubv_to_int x) (ubv_to_int y))))))
(define-fun bvxor ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (+ (ubv_to_int x) (ubv_to_int y) (* (- 2) (& (ubv_to_int x) (ubv_to_int y))))))
(define-fun bvnand ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k) (bvnot (bvand x y)))
(define-fun bvnor  ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k) (bvnot (bvor x y)))
(define-fun bvxnor ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k) (bvnot (bvxor x y)))
```

Comparisons:

```
(define-fun bvule ((x (_ BitVec k)) (y (_ BitVec k))) Bool (<= (ubv_to_int x) (ubv_to_int y)))
(define-fun bvult ((x (_ BitVec k)) (y (_ BitVec k))) Bool (< (ubv_to_int x) (ubv_to_int y)))
(define-fun bvuge ((x (_ BitVec k)) (y (_ BitVec k))) Bool (<= (ubv_to_int y) (ubv_to_int x)))
(define-fun bvugt ((x (_ BitVec k)) (y (_ BitVec k))) Bool (< (ubv_to_int y) (ubv_to_int x)))
(define-fun bvsle ((x (_ BitVec k)) (y (_ BitVec k))) Bool (<= (sbv_to_int x) (sbv_to_int y)))
(define-fun bvslt ((x (_ BitVec k)) (y (_ BitVec k))) Bool (< (sbv_to_int x) (sbv_to_int y)))
(define-fun bvsge ((x (_ BitVec k)) (y (_ BitVec k))) Bool (<= (sbv_to_int y) (sbv_to_int x)))
(define-fun bvsgt ((x (_ BitVec k)) (y (_ BitVec k))) Bool (< (sbv_to_int y) (sbv_to_int x)))
(define-fun bvcomp ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec 1)
   (ite (= x y) (_ bv1 1) (_ bv0 1)))
```

Miscellaneous:

```
(define-fun (_ zero_extend i) ((x (_ BitVec k))) (_ BitVec i+k)
   ((_ int_to_bv (i+k)) (ubv_to_int x)))
(define-fun (_ sign_extend i) ((x (_ BitVec k))) (_ BitVec i+k)
   ((_ int_to_bv (i+k)) (sbv_to_int x)))
(define-fun concat ((x (_ BitVec k1)) (y (_ BitVec k2))) (_ BitVec k1+k2)
   ((_ int_to_bv (k1+k2)) (+ (* (2^k2) (ubv_to_int x)) (ubv_to_int y))))
(define-fun (_ extract i j) ((x (_ BitVec k1))) (_ BitVec i-j+1)
   ((_ int_to_bv (i-j+1)) (div (ubv_to_int x) 2^j)))
(define-fun (_repeat i) ((x (_ BitVec k))) (_ BitVec i*k)
   ((_ int_to_bv (i*k)) (* ((2^(i*k)-1)/(2^k-1)) (ubv_to_int x))))
(define-fun (_ rotate_left i)  ((x (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (+ (* 2^(i mod k) (ubv_to_int x)) (div (ubv_to_int x) 2^(-i mod k)))))
(define-fun (_ rotate_right i)  ((x (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (+ (* 2^(-i mod k) (ubv_to_int x)) (div (ubv_to_int x) 2^(i mod k)))))
```
