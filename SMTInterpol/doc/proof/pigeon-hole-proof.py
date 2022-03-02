#!/usr/bin/env python3

def smt2_header():
    return """\
; Boolean Pigeon Hole Problem in SMT format
;
; Variables p_n_i_j states pigeon i sits in hole j
;   where n is number of holes, 0<=i<=n, 1<=j<=n
; Clauses are
;   (or p_n_i_1 ... p_n_i_n)   for  0<=i<=n.
;     (every pigeon sits in a hole)
;   (or (not p_n_i_j) (not p_n_i'_j)) for 0<=i<i'<=n,1<=j<=n
;     (no two pigeons sit in the same hole
"""

def proof_header():
    return"""\
; Extended resolution proof for Pigeon Hole Problem.
; Problem for n pigeons is transformed to a problem for n-1 pigeons.
; Variable p_n_i_j states that pigeon i sits in hole j
;   where n is number of holes, 0<=i<=n, 1<=j<=n
; A_n_i proves (+ p_n_i_1 ... + p_n_i_n)   for  0<=i<=n.
;   stating that every pigeon sits in a hole.
; B_n_i_i'_j proves   (- p_n_i_j  - p_n_i'_j) for 0<=i<i'<=n,1<=j<=n
;   stating that no two pigeons sit in the same hole.
; Reduction to n-1 is done by swapping pigeon n with the pigeon that
; sits in hole n and then proving the clauses A, B for n-1.
"""

# Create a proof for the pigeon-hole problem.

def clause_A(n,i):
    clause = " ".join([f"p_{n}_{i}_{j}" for j in range(1,n+1)])
    return clause
    
def create_A(n,i):
    clause = clause_A(n,i)
    if n > 1:
        clause = f"(or {clause})"
    return clause

def create_B(n,i,j,k):
    return f"(or (not p_{n}_{i}_{k}) (not p_{n}_{j}_{k}))"


def declare_input_clauses(n, f):
    for i in range(0, n + 1):
        print(f"(assert {create_A(n,i)})", file=f)
    for i in range(0, n + 1):
        for j in range(i + 1, n + 1):
             for k in range(1, n + 1):
                 print(f"(assert {create_B(n,i,j,k)})", file=f)

def create_input_clauses(n, f, assertcmd="assert"):
    print("(let-proof (", file=f)
    for i in range(0, n + 1):
        clause = clause_A(n,i)
        print(f"  (A_{n}_{i} (let ((cl (or {clause}))) (res cl ({assertcmd} cl) (or- {clause}))))", file=f)

    for i in range(0, n + 1):
        for j in range(i + 1, n + 1):
             for k in range(1, n + 1):
                 p1=f"p_{n}_{i}_{k}"
                 p2=f"p_{n}_{j}_{k}"
                 print(f"  (B_{n}_{i}_{j}_{k} (let ((np1 (not {p1})) (np2 (not {p2}))) (let ((cl (or np1 np2))) (res np1 (res np2 (res cl ({assertcmd} cl) (or- np1 np2)) (not- {p2})) (not- {p1})))))", file=f)
    print (f"  )", file=f)

def create_layer(l, f):
    print("(let (", file=f)
    for i in range(0, l):
        for k in range(1, l):
            print(f"  (q_{l}_{i}_{k} (and p_{l}_{i}_{l} p_{l}_{l}_{k}))", file=f)
    print("  )", file=f)
    print("(let (", file=f)
    for i in range(0, l):
        for k in range(1, l):
            print(f"  (p_{l-1}_{i}_{k} (or p_{l}_{i}_{k} q_{l}_{i}_{k}))", file=f)
    print("  )", file=f)
    print("(let-proof (", file=f)
    for i in range(0, l):
        for k in range(1, l):
            print(f"  (C1_{l}_{i}_{k} (res q_{l}_{i}_{k} (or- p_{l}_{i}_{k} q_{l}_{i}_{k}) (and- 1 p_{l}_{i}_{l} p_{l}_{l}_{k})))", file=f)
            print(f"  (C2_{l}_{i}_{k} (res p_{l}_{i}_{k} (res q_{l}_{i}_{k} (or- p_{l}_{i}_{k} q_{l}_{i}_{k}) (and- 0 p_{l}_{i}_{l} p_{l}_{l}_{k})) B_{l}_{i}_{l}_{k}))", file=f)
    print("  )", file=f)
    print("(let-proof (", file=f)
    for i in range(0, l):
        for j in range(i + 1, l):
            for k in range(1, l):
                print(f"""\
  (B_{l-1}_{i}_{j}_{k}
    (res p_{l}_{l}_{k}
      (res p_{l}_{i}_{k} C1_{l}_{i}_{k}
        (res p_{l}_{j}_{k} C1_{l}_{j}_{k} B_{l}_{i}_{j}_{k}))
      (res p_{l}_{i}_{l} C2_{l}_{i}_{k}
        (res p_{l}_{j}_{l} C2_{l}_{j}_{k} B_{l}_{i}_{j}_{l}))))""", file=f)
    for i in range(0, l):
        proof = f"(res p_{l}_{l}_{l} A_{l}_{l} B_{l}_{i}_{l}_{l})"
        for j in range(l-1, 0, -1):
            proof = f"(res p_{l}_{l}_{j} {proof} (and+ p_{l}_{i}_{l} p_{l}_{l}_{j}))"
        proof = f"(res p_{l}_{i}_{l} A_{l}_{i} {proof})";
        for j in range(l-1, 0, -1):
            proof = f"(res p_{l}_{i}_{j} {proof} (or+ 0 p_{l}_{i}_{j} q_{l}_{i}_{j}))"
            proof = f"(res q_{l}_{i}_{j} {proof} (or+ 1 p_{l}_{i}_{j} q_{l}_{i}_{j}))"
        print(f"  (A_{l-1}_{i} {proof})", file=f);
    print("  )", file=f)

def simple_proof(l, f):
    proof = f"A_{l}_{l}"
    for i in range(1, l + 1):
        print(f"(res p_{l}_{l}_{i}", file=f)
    print(f"A_{l}_{l}", file=f)
    for i in range(l, 0, -1):
        def renamebox(k):
            return k + 1 if k >= i else k
        renamep = " ".join([" ".join([
            f"(p_{l-1}_{j}_{k} p_{l}_{j}_{renamebox(k)})"
            for j in range(0,l)]) for k in range(1, l)])
        proofA = " ".join([
            f"(A_{l-1}_{j} (res p_{l}_{j}_{i} A_{l}_{j} B_{l}_{j}_{l}_{i}))"
            for j in range(0, l)
            ])
        renameB = " ".join([" ".join([" ".join([
            f"(B_{l-1}_{j1}_{j2}_{k} B_{l}_{j1}_{j2}_{renamebox(k)})"
            for k in range(1,l)])
            for j2 in range(j1+1, l)]) for j1 in range(0, l)])
        print(f"(let ({renamep}) (let-proof ({renameB} {proofA})", file=f)
        full_proof(l-1, f)
        print("))", file=f)
    
def full_proof(l, f):
    if l > 1:
        create_layer(l, f)
        full_proof(l-1, f)
        print("  ))))", file=f)
    elif l > 1:
        simple_proof(l)
    else:
        print("    (res p_1_0_1 A_1_0 (res p_1_1_1 A_1_1 B_1_0_1_1))", file=f)

def pigeon_hole(n, f, assertcmd="assert"):
    create_input_clauses(n, f, assertcmd=assertcmd)
    full_proof(n, f)
    print(" )", file=f)


def simplify_proof(n, f, asproof=True):
    print("(set-logic QF_UFLIA)", file=f)
    print("(declare-sort Proof 0)", file=f)
    if not asproof:
        print("(declare-fun assume (Bool) Proof)", file=f)
        print("(declare-fun res (Bool Proof Proof) Proof)", file=f)
        print("(declare-fun check (Proof) Bool)", file=f)
        print("(declare-fun or+ (Int Bool Bool) Proof)", file=f)
        print("(declare-fun or- (Bool Bool) Proof)", file=f)
        print("(declare-fun and+ (Bool Bool) Proof)", file=f)
        print("(declare-fun and- (Int Bool Bool) Proof)", file=f)
    for i in range(0, n+1):
        for k in range(1, n+1):
            print(f"(declare-fun p_{n}_{i}_{k} () Bool)", file=f)
    if asproof:
        declare_input_clauses(n, file=f)
        print("(check-proof")
        pigeon_hole(n, f, assertcmd="assume")
        print(")", file=f)
    else:
        print("(assert (check", file=f)
        pigeon_hole(n, f, assertcmd="assume")
        print("))", file=f)


def printsmt2(n,f):
    print(smt2_header(), file=f)
    print("(set-option :produce-proofs true)", file=f)
    print("(set-logic QF_UF)", file=f)
    for i in range(0, n+1):
        for k in range(1, n+1):
            print(f"(declare-fun p_{n}_{i}_{k} () Bool)", file=f)
    declare_input_clauses(n,f)
    print("(check-sat)", file=f)
    print("(get-proof)", file=f)

def printproof(n,f):
    print(proof_header(), file=f)
    print("unsat", file=f)
    pigeon_hole(n, f, assertcmd="assume")

if __name__ == "__main__":
    import sys
    n = int(sys.argv[1])
    with open(f"pigeon-hole-{n}.smt2", "w") as f:
        printsmt2(n, f)
    with open(f"pigeon-hole-{n}.proof", "w") as f:
        printproof(n, f)

