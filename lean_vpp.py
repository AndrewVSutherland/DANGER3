#!/usr/bin/env python3

# This program was written by Claude Opus 4.6 in April, 2026

"""
Generate a Lean 4 / Mathlib proof that (p, A, x₀) is a Pomerance triple.

Usage:
    python3 lean_vpp.py p A x0 [output.lean]

If no output file is given, prints to stdout.
"""

import sys
from math import gcd, isqrt


def ext_gcd(a: int, b: int) -> tuple[int, int, int]:
    """Extended GCD: returns (g, s, t) with s*a + t*b = g."""
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    return old_r, old_s, old_t


def verify_and_trace(p: int, A: int, x0: int):
    """Run the Pomerance verification and collect all intermediate data."""
    assert p >= 5 and p % 2 == 1, f"p must be odd and >= 5, got {p}"

    q = isqrt(p)
    assert q * q <= p < (q + 1) ** 2
    k = (q + 1 + isqrt(4 * q)).bit_length()
    s = isqrt(4 * q)
    assert s * s <= 4 * q < (s + 1) ** 2
    assert q + 1 + s < 2 ** k

    if p % 4 == 3:
        inv4 = (p + 1) // 4
    else:
        inv4 = (3 * p + 1) // 4
    C = ((A + 2) * inv4) % p
    assert (4 * C) % p == (A + 2) % p

    disc = A * A - 4
    assert gcd(disc, p) == 1, f"gcd(A²-4, p) = {gcd(disc, p)}, curve is singular"
    g1, sa, ta = ext_gcd(disc, p)
    assert g1 == 1 and sa * disc + ta * p == 1

    X, Z = x0 % p, 1
    steps = [(X, Z)]
    for i in range(k):
        U = (X + Z) ** 2 % p
        V = (X - Z) ** 2 % p
        W = U - V
        Xn = U * V % p
        Zn = W * (V + C * W) % p
        steps.append((Xn, Zn))
        X, Z = Xn, Zn

    Zprev = steps[-2][1]
    Zfinal = steps[-1][1]
    assert Zfinal % p == 0, f"Final Z = {Zfinal}, not 0 mod p"
    assert gcd(Zprev, p) == 1, f"gcd(Zprev, p) = {gcd(Zprev, p)}, not 1"
    g2, sz, tz = ext_gcd(Zprev, p)
    assert g2 == 1 and sz * Zprev + tz * p == 1

    return {
        "p": p, "A": A, "x0": x0, "C": C, "k": k, "q": q, "s": s,
        "steps": steps, "Zprev": Zprev,
        "bez_disc": (sa, ta), "bez_zprev": (sz, tz),
    }


def generate_lean(data: dict) -> str:
    """Generate the Lean 4 proof file from traced data."""
    p = data["p"]
    A = data["A"]
    x0 = data["x0"]
    C = data["C"]
    k = data["k"]
    q = data["q"]
    s = data["s"]
    steps = data["steps"]
    Zprev = data["Zprev"]
    sa, ta = data["bez_disc"]
    sz, tz = data["bez_zprev"]
    X0, Z0 = steps[0]
    Xfinal, Zfinal = steps[-1]

    L = []

    # ── Preamble (definitions, only emitted once) ──────────────────────
    L.append("import Mathlib.Tactic.NormNum")
    L.append("")
    L.append("def mongDbl (p C X Z : ℤ) : ℤ × ℤ :=")
    L.append("  let U := (X + Z) ^ 2 % p")
    L.append("  let V := (X - Z) ^ 2 % p")
    L.append("  let W := U - V")
    L.append("  (U * V % p, W * (V + C * W) % p)")
    L.append("")
    L.append("def mongIter (p C : ℤ) : ℕ → ℤ → ℤ → ℤ × ℤ × ℤ")
    L.append("  | 0, X, Z => (X, Z, 0)")
    L.append("  | n + 1, X₀, Z₀ =>")
    L.append("    let prev := mongIter p C n X₀ Z₀")
    L.append("    let next := mongDbl p C prev.1 prev.2.1")
    L.append("    (next.1, next.2, prev.2.1)")
    L.append("")
    L.append("theorem mongIter_step (p C : ℤ) (n : ℕ) (X₀ Z₀ Xn Zn Xn1 Zn1 Zp : ℤ)")
    L.append("    (hprev : mongIter p C n X₀ Z₀ = (Xn, Zn, Zp))")
    L.append("    (hdbl : mongDbl p C Xn Zn = (Xn1, Zn1)) :")
    L.append("    mongIter p C (n + 1) X₀ Z₀ = (Xn1, Zn1, Zn) := by")
    L.append("  show (let prev := mongIter p C n X₀ Z₀")
    L.append("        let next := mongDbl p C prev.1 prev.2.1")
    L.append("        (next.1, next.2, prev.2.1)) = _")
    L.append("  rw [hprev]; dsimp only []; rw [hdbl]")
    L.append("")
    L.append("structure PomeranceCert where")
    L.append("  p : ℤ")
    L.append("  A : ℤ")
    L.append("  x₀ : ℤ")
    L.append("  C : ℤ")
    L.append("  k : ℕ")
    L.append("  q : ℕ")
    L.append("  s : ℕ")
    L.append("  bez_disc : ℤ × ℤ")
    L.append("  bez_zprev : ℤ × ℤ")
    L.append("")
    L.append("def PomeranceCert.Valid (d : PomeranceCert) : Prop :=")
    L.append("  5 ≤ d.p ∧")
    L.append("  d.p % 2 = 1 ∧")
    L.append("  d.bez_disc.1 * (d.A ^ 2 - 4) + d.bez_disc.2 * d.p = 1 ∧")
    L.append("  4 * d.C % d.p = (d.A + 2) % d.p ∧")
    L.append("  (d.q : ℤ) ^ 2 ≤ d.p ∧")
    L.append("  d.p < ((d.q : ℤ) + 1) ^ 2 ∧")
    L.append("  d.s ^ 2 ≤ 4 * d.q ∧")
    L.append("  4 * d.q < (d.s + 1) ^ 2 ∧")
    L.append("  d.q + 1 + d.s < 2 ^ d.k ∧")
    L.append("  let (_, Z, Zprev) := mongIter d.p d.C d.k (d.x₀ % d.p) 1")
    L.append("  Z % d.p = 0 ∧")
    L.append("  d.bez_zprev.1 * Zprev + d.bez_zprev.2 * d.p = 1")
    L.append("")
    L.append("def IsPomeranceTriple (p A x₀ : ℤ) : Prop :=")
    L.append("  ∃ d : PomeranceCert, d.p = p ∧ d.A = A ∧ d.x₀ = x₀ ∧ d.Valid")
    L.append("")

    # ── Certificate-specific proof ─────────────────────────────────────
    L.append(f"/-!")
    L.append(f"## Certificate for p = {p} ({p.bit_length()} bits)")
    L.append(f"  k = {k} doublings, q = {q}, s = {s}, C = {C}")
    L.append(f"-/")
    L.append("")

    # Doubling lemmas
    for i in range(k):
        Xi, Zi = steps[i]
        Xn, Zn = steps[i + 1]
        L.append(
            f"private lemma dbl{i} : mongDbl {p} {C} {Xi} {Zi} "
            f"= ({Xn}, {Zn}) := by norm_num [mongDbl]"
        )
    L.append("")

    # Chained iteration lemmas
    L.append(
        f"private lemma iter0 : mongIter {p} {C} 0 {X0} {Z0} "
        f"= ({X0}, {Z0}, 0) := rfl"
    )
    for i in range(k):
        Xn, Zn = steps[i + 1]
        Zprev_i = steps[i][1]
        L.append(
            f"private lemma iter{i+1} : mongIter {p} {C} {i+1} {X0} {Z0} "
            f"= ({Xn}, {Zn}, {Zprev_i}) :="
        )
        L.append(f"  mongIter_step _ _ _ _ _ _ _ _ _ _ iter{i} dbl{i}")
    L.append("")

    # Main theorem
    L.append(f"theorem pomerance_{p} : IsPomeranceTriple {p} {A} {x0} := by")
    L.append(
        f"  refine ⟨⟨{p}, {A}, {x0}, {C}, {k}, {q}, {s}, "
        f"({sa}, {ta}), ({sz}, {tz})⟩, rfl, rfl, rfl, ?_⟩"
    )
    L.append(
        f"  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,"
    )
    L.append(
        f"          by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩"
    )
    L.append(
        f"  rw [show ({X0} : ℤ) % {p} = {X0} from by norm_num]"
    )
    L.append(f"  rw [iter{k}]")
    L.append(f"  exact ⟨by norm_num, by norm_num⟩")

    return "\n".join(L) + "\n"


def main():
    if len(sys.argv) < 4:
        print(f"Usage: {sys.argv[0]} p A x0 [output.lean]", file=sys.stderr)
        sys.exit(1)

    p, A, x0 = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    outfile = sys.argv[4] if len(sys.argv) > 4 else None

    data = verify_and_trace(p, A, x0)
    lean = generate_lean(data)

    bits = p.bit_length()
    k = data["k"]
    print(f"p = {p} ({bits} bits), k = {k} doublings", file=sys.stderr)

    if outfile:
        with open(outfile, "w") as f:
            f.write(lean)
        print(f"Wrote {outfile}", file=sys.stderr)
    else:
        print(lean)


if __name__ == "__main__":
    main()
