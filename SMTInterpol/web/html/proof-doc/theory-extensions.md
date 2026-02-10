## Extensions for other theories

When adding more theories, we need to add more axioms to support
these theories.  Here we will look into some of them.

### Array Theory

We add the McCarthy axioms and an axiom for extensionality.  We choose
the axiom with an explicit `@diff` operator that returns some index where
two arrays differ, if they differ.

```
⟨array-axiom⟩ ::=
 | (selectstore1 a i v)   ;( +(= (select (store a i v) i) v) )
 | (selectstore2 a i j v) ;( +(= (select (store a i v) j) (select a j)) +(= i j))
 | (extdiff a b)   ;( +(= a b) -(= (select a (@diff a b)) (select b (@diff a b))))
```

For supporting const arrays one additional axiom is needed:

```
 | (const v i)  ;( +(= (select (@const v) i) v) )
```

### Arithmetic

For arithmetic we need to manipulate polynomials.  Polynomials are
represented by an SMT-LIB term of the following form.

```
  (+ (* c1 t11 … t1m) … (* cn tn1 … tnm))
```

Here c1, .., cn are constants (NUMERALS, DECIMALS, or integer/real
numbers in canonical form).  All `(ti1 … tim)` are different multi-sets,
the head symbol of tij is not `+` or `*`.  All ci,tij have the same type
(Real or Int). The constant `ci` can be omitted, if it
is 1 (except if there is no `ti1 … tin`), `*`/`+` is omitted if it has only
one argument. The zero polynomial is represented by 0.

When multiplying polynomials or adding them together the usual rules of
distributivity, commutativity and associativity are applied to bring them
into the above normal form again.

We have four rules that manipulate these polynomial.  The first two
are doing polynom addition and multiplication:

```
⟨arith-axiom⟩ ::=
 | (poly+ (+ a1 … an) a):  ;( +(= (+ a1 … an) a) )  where a1+…+an = a
 | (poly* (* a1 … an) a):  ;( +(= (* a1 … an) a) )  where a1*…*an = a
 | …
```

Here `a1`, ..., `an`, `a` are polynomials.  The side-condition
`a1+…+an=a` states that the polynomial resulting from adding `a1` to
`an` together yields a polynomial equal to `a`, i.e. has the same
monomials with the same coefficients, but can differ in the order of
the terms.  Similarly for `a1*…*an=a`.

Then we have one rule for `to_real`:

```
⟨arith-axiom⟩ ::= …
 | (to_real-def a)  ;( +(= (to_real a) a') )
```

where `a` is a polynomial `(+ … (* ci … tij …))` with integer terms
and `a'` is the polynomial `(+ … (* ci' … (to_real tij) …))`
where `ci'` is the real representation of the integer `ci`, i.e.,
an integer `NUM` is replaced with `NUM.0`
and `(- NUM)` is replaced with `(- NUM.0)`.  Every other term t is replaced
by (to_real t).

The heart of the proof system is the following rule proving the
inconsistency between multiple inequalities by using Farkas' Lemma.
(Note that this is only complete for linear arithmetic).

```
⟨arith-axiom⟩ ::= …
 | (farkas c1 (<=? a1 b1) … cn (<=? an bn)): ( -(<=? a1 b1) … -(<=? an bn) )
```

where `ci` are positive integers, `<=?` stands for `<`, `<=`, or `=`,
`ai`,`bi` are polynomials.  The weighted sum of these polynomials,
`c1*(a1-b1) + ... + cn*(an-bn)` is a (rational or integer) constant `c`
where `c >= 0`.  If `c = 0`, then at least one inequality must be strict.
If some inequalities are Int and some are Real, all inequalites are
implicitly converted to Real by converting all coefficients in ai/bi to
real and replacing all terms t in ai/bi with (to_real t).

The remaining axioms work with arbitrary terms and do not require adding
or multiplying polynomials:

```
⟨arith-axiom⟩ ::= …
 | (trichotomy a b)   ;( +(< a b) +(= a b) +(< b a) )
 | (total a b)        ;( +(<= a b), (< b a) )
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
an arbitrary term of sort `Int`.  Remark: an alternative would be to
restrict the axiom to c=0, i.e., `(total-int a)`  proves `( +(<= a 0) +(<= 1 a) )`

Also we need the following axioms for handling division and modulo.
The rules are for the theories that contain the corresponding function
symbols.  Note that these rules are syntactically.  No polynomial
normalization is performed int these rules.

```
⟨arith-axiom⟩ ::= …
 | (/def a b1 ... bn) ;( +(= a (* b1 ... bn (/ a b1 ... bn))) +(= b1 0) ... +(= bn 0) )
 | (div-low x d):       ;( +(<= (* d (div x d)) x) +(= d 0) )
 | (div-high x d):      ;( +(<  x (+ (* d (div x d)) (abs d))) +(= d 0) )
 | (mod-def x d):       ;( +(= (mod x d) (- x (* d (div x d)))) +(= d 0) )
 | (to_int-low x):      ;( +(<= (to_real (to_int x)) x) )
 | (to_int-high x):     ;( +(<  x (+ (to_real (to_int x)) 1.0)) )
)
```

In addition to the axioms above we also add new definitions for the
`expand` axioms.   These are given in the following table

```
(define-fun - ((x Int)) Int (* (- 1) x))
(define-fun - ((x Real)) Real (* (- 1) x))
(define-fun - ((x Int) Int (y Int)) (+ x (* (- 1) y)))
(define-fun - ((x Real) Real (y Real)) (+ x (* (- 1.0) y)))
(define-fun > ((x Int) Bool (y Int)) (< y x))
(define-fun > ((x Real) Bool (y Real)) (< y x))
(define-fun >= ((x Int) Bool (y Int)) (<= y x))
(define-fun >= ((x Real) Bool (y Real)) (<= y x))
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
reals, the functions for automatically casting the to real are
defined.  This is also supported by the expand function, even if
the function is not used with more than two arguments.
Here `i0`, `i2` are terms of sort `Int` and `r1`, `r3` are terms of
sort `Real`.

```
(expand (+ i0 r1 i2 r3)): ( +(= (+ i0 r1 i2 r3)
                                 (+(to_real i0) r1 (to_real i2) r3)))
```

Note that the axiom `farkas` is the only axiom with negated literals.
It can be used in a resolution proof to rewrite a positive literals
into the corresponding negative literal.  On the other hand, the
axiom `total` and `total-int` can be used to rewrite a negative literal
into the corresponding positive literal.

### Data Types

For reasoning about data types, the following rules are used

```
⟨datatype-axiom⟩ ::= …
 | (dt_project seli a1 … an)       ;( +(= (seli (cons a1 ... an)) ai) )
 | (dt_cons cons x)                ;( -((_ is cons) x) +(= (cons (sel1 x) ... (seln x)) x) )
 | (dt_test cons (cons a1 … an))   ;( +((_ is cons) (cons a1 ... an)) )
 | (dt_test cons' (cons a1 … an))  ;( -((_ is cons') (cons a1 ... an)) )
 | (dt_exhaust x)                  ;( +((_ is cons1) x) ... +((_ is consn) x) )
 | (dt_acyclic (cons …(cons… x …)…) x) ;( -(= (cons …(cons… x …)…) x) )
   ; where (cons …(cons… x …)…) is a term containing x and on the around x
   ; only constructor functions appear.
 | (dt_match (match t …))
   ;( +(= (match t ((p1 x1) c1) …) (ite ((_ is p1) t) (let (x1 (sel1 t)) c1) …)) )
```

### Bit Vectors

The idea is to translate bit vectors into integer arithmetic.  We make
use of the new functions `ubv_to_int` and `int_to_bv` to convert
between integers and bitvectors.

We have the following correspondences:

```
⟨bitvector-axiom⟩ ::=
 | (int2ubv2int k t0)  ;( +(= (ubv_to_int ((_ int_to_bv k) t0)) (mod t0 2^k)) )
 | (int2sbv2int k t0)  ;( +(= (sbv_to_int ((_ int_to_bv k) t0)) (+ (mod (+ t0 2^(k-1)) 2^k) (- 2^(k-1)))) )
 | (ubv2int2bv t0)     ;( +(= ((_ int_to_bv k) (ubv_to_int t0)) t0)    where a is of type (_ BitVec k)
```

In these axioms 2^k, 2^(k-1) stand for the corresponding numerals,
e.g., for $k=3$ the axiom `(int2sbv2int 3 t0)` proves the clause
`( +(= (sbv_to_int ((_ int_to_bv 3) t0)) (+ (mod (+ t0 4) 8) (- 4))))`.
The axiom is syntactic, i.e., the term `(+ t0 4)` is not simplified.

The following definitons handle arithmetic:
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
            (ite (< iy 0) (div (- ix) (- iy)) (ite (= iy 0) 1 (- (div (- ix) iy))))
            (ite (< iy 0) (- (div ix (- iy))) (ite (= iy 0) (- 1) (div ix iy)))))))
(define-fun bvsrem ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   (let ((ix (sbv_to_int x)) (iy (sbv_to_int y)))
   ((_ int_to_bv k) (ite (= iy 0) ix
            (ite (< ix 0) (- (mod (- ix) iy)) (mod ix iy))))))
(define-fun bvsmod ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   (let ((ix (sbv_to_int x)) (iy (sbv_to_int y)))
   ((_ int_to_bv k) (ite (= iy 0) ix (ite (< iy 0) (+ (mod (+ ix (- 1)) (- iy)) iy 1) (mod ix iy)))))
(define-fun bvnego ((x (_ BitVec k))) Bool
   (= (ubv_to_int x) 2^(k-1)))
(define-fun bvuaddo ((x (_ BitVec k)) (y (_ BitVec k))) Bool
   (<= 2^k (+ (ubv_to_int x) (ubv_to_int y))))
(define-fun bvsaddo ((x (_ BitVec k)) (y (_ BitVec k))) Bool
   (or (< (+ (sbv_to_int x) (sbv_to_int y)) 2^(k-1)) (<= 2^(k-1) (+ (sbv_to_int x) (sbv_to_int y)))))
(define-fun bvumulo ((x (_ BitVec k)) (y (_ BitVec k))) Bool
   (<= 2^k (* (ubv_to_int x) (ubv_to_int y))))
(define-fun bvsmulo ((x (_ BitVec k)) (y (_ BitVec k))) Bool
   (or (< (* (sbv_to_int x) (sbv_to_int y)) 2^(k-1)) (<= 2^(k-1) (* (sbv_to_int x) (sbv_to_int y)))))
(define-fun bvsdivo ((x (_ BitVec k)) (y (_ BitVec k))) Bool
   (and (= (ubv_to_int x) 2^(k-1)) (= (sbv_to_int y) (- 1))))
(define-fun bvusubo ((x (_ BitVec k)) (y (_ BitVec k))) Bool
   (< (ubv_to_int x) (ubv_to_int y)))
(define-fun bvssubo ((x (_ BitVec k)) (y (_ BitVec k))) Bool
   (or (< (sbv_to_int x) (+ (sbv_to_int y)) 2^(k-1)) (<= (+ (sbv_to_int y) 2^(k-1)) (sbv_to_int x))))
```

For shifts, we define a function `pow2` for shifts and its inverse `log2`. We add a few axioms.

```
⟨bitvector-axiom⟩ ::=
 | (pow2const k) ;( +(= (pow2 k) 2^k) )    # where 0<=k is a constant
 | (pow2add n m) ;( -(<= 0 n) -(<= 0 m) +(= (pow2 (+ n m)) (* (pow2 n) (pow2 m))) )
 | (log2low a)   ;( -(<= 0 a) +(<= (pow2 (log2 a)) a) )
 | (log2high a)  ;( -(<= 0 a) +(< a (* 2 (pow2 (log2 a)))) )
```

```
(define-fun bvshl ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (* (pow2 (ubv_to_int y)) (ubv_to_int x)))
(define-fun bvlshr ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (div (ubv_to_int x) (pow2 (ubv_to_int y))))
(define-fun bvashr ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k)
   ((_ int_to_bv k) (div (sbv_to_int x) (pow2 (ubv_to_int y))))
```

For logical operations we use a new integer binary and
`:funs (& Int Int Int :left-assoc)`, that computes logical and for
integers.  It returns a negative number if and only if both arguments
are negative and ensures that no bits are truncated before doing the
logical and.

```
⟨bitvector-axiom⟩ ::=
 | (&flat (& (& a_ij)) (& bi))
      ;( +(= (& (& a_11 ...) ... (& an1 ...)) (& b_1 ... b_m)) ) where {b_i} \union {-1} = { a_ij }
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
   ((_ int_to_bv k) (+ (ubv_to_int x) (ubv_to_int y) (* (- 2) (&
   (ubv_to_int x) (ubv_to_int y))))))
(define-fun bvnand ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k) (bvnot (bvand x y))
(define-fun bvnor  ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k) (bvnot (bvor x y))
(define-fun bvxnor ((x (_ BitVec k)) (y (_ BitVec k))) (_ BitVec k) (bvnot (bvxor x y))
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
   (ite (= x y) (_ bv1 1) (_ bv0 0)))
```

Miscellanous:

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
