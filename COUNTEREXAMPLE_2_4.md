# A counterexample to Sun's Conjecture 2.4(ii) (arXiv:1208.2683)

**Statement (Sun, 2012-08-17).** Let a < 0 be an integer that is not a perfect power. Let p_1(a) < p_2(a) < … be
the primes p for which a is the *largest negative primitive root* modulo p. This means that a is a primitive
root mod p and no b with a < b < 0 is one. Then p_{n+1}(a) < p_n(a)^{1+1/n}, "with the only exception a = −2
and n = 13".

**Counterexample.** a = −3, n = 754 589:

    p_n(−3)     = 51 459 203
    p_{n+1}(−3) = 51 460 433        (gap 1230)
    n · log(p_{n+1}/p_n) = 18.03629523…  >  log p_n = 17.75629987…

So p_{n+1}(−3) > p_n(−3)^{1+1/n}, with r = n log(p_{n+1}/p_n) / log p_n = 1.015768789…

Equivalently, in a form close to Sun's: ⁿ√(p_n) < ⁿ⁺¹√(p_{n+1}) for n = 754 589. The Firoozbakht-type
inequality fails by 1.6%, since the allowed gap is p_n log p_n / n ≈ 1211.

## Verification (three independent routes)

1. `proot_firoz.c` (C). Segmented sieve, trial-division factorisation of p − 1, and a primitive-root test
   g^{(p−1)/q} ≢ 1 for every prime q | p − 1. It scans all primes up to 10⁹, a ∈ [−60, 60]. It also
   reproduces Sun's exception a = −2, n = 13 (103 → 149).
2. `verify_proot.py` (Python + numpy + mpmath). Smallest-prime-factor sieve, Python `pow`, recount from p = 3,
   and a 60-digit comparison. It confirms n = 754 589 and that 51 460 433 is the next member.
3. sympy `isprime` / `is_primitive_root`:
   - both numbers are prime;
   - −1 and −2 are not primitive roots of either, and −3 is;
   - no prime strictly between them has this property;
   - the same definition gives Sun's sequence 5, 7, 13, 23, … with the exception at n = 13.

## Scan results (X = 10⁹, `proot_1e9.txt`)

- **Part (i), a > 0:** no violation for any a ≤ 60. The closest cases are r = 0.980 (a = 2, n = 2) and
  r = 0.958 (a = 3, p = 291 857).
- **Part (ii), a < 0:** violations only at a = −2, n = 13 (Sun's exception) and **a = −3, n = 754 589 (new)**.
  The next closest is a = −9, with r = 0.943.

## Why this was predicted

The primes with a prescribed least primitive root have density c_a / log x, the same shape as the primes.
- *Typical case:* the Firoozbakht-type inequality allows a gap of mean·log p, while the typical largest gap is
  mean·log n.
- *Violations:* they need a Gumbel fluctuation of size ≈ log(1/c_a) + log log p. This happens with probability
  ≈ c_a / log p per dyadic scale, so violations are expected infinitely often, but rarely
  (`research/root_monotonicity/THEOREM.md`, dual family).
- *Where:* the scan covered about 120 such sequences, which made a hit within reach.

## Lean formalisation (`Sunproj/PrimRoot/`)

`Sun24.lean` proves `PrimRoot.sun24ii_false : ¬ SunConj24ii`. The statement uses Mathlib notions:
- `IsPrimRoot a p := orderOf (a : ZMod p) = p - 1`;
- `IsLNPR a p` (p prime, a a primitive root, no b with a < b < 0 one);
- `sunP a n := Nat.nth (IsLNPR a) (n - 1)`.

`sun24ii_counterexample` gives an n ≥ 754 589 with sunP(−3, n) = 51 459 203, sunP(−3, n+1) = 51 460 433 and
51459203^(1+1/n) < 51460433 in ℝ.

**The certificate.** The exact value of n is not needed. Both primes are fixed, and the inequality fails
for every n ≥ 742 875, so a *lower* bound on the count suffices. The lower bound needs only membership
certificates, never non-membership certificates for the ~5·10⁷ other integers.

| file | content |
|---|---|
| `SmallPrimes.lean` | bitmask of the odd primes < 2¹⁶, validated by kernel trial division |
| `Checker.lean` | Boolean checker plus soundness proofs: Lucas (`lucas_primality`, `orderOf_eq_of_pow_and_pow_div_prime`); −2 handled via `ZMod.exists_sq_eq_neg_two_iff` or an order witness; `run_sound`, `runGap_sound` |
| `Data/C000–C377.lean` | 754 589 member certificates in 378 chunks, each checked with `decide +kernel` |
| `Gap.lean` | 51 459 203 and 51 460 433 are members; the 1229 integers in between are not (proper divisor, an order witness for −3, or a Lucas proof that −2 is a primitive root) |
| `Sun24.lean` | chains the chunks: count ≥ 754 589; Nat.nth bookkeeping; kernel check 51459203^754590 < 51460433^754589; passage to ℝ |

**Per-member certificate.** For a member p it gives:
- the odd prime factors of p − 1 below 2¹⁶;
- the cofactor, which the checker computes as (p−1)/gcd(p−1, rad³²) and which is 1 or a prime with a
  nested Lucas certificate;
- a witness for −2.

The −3 test checks (−3)^((p−1)/2) ≡ −1 and (−3)^((p−1)/r) ≢ 1, so it proves primality and the primitive
root at once.

**Trust base.** There is no `sorry` and no `native_decide`; the axioms are propext, Classical.choice and
Quot.sound. Generator: `scripts/sun24/gen_data.py`, `scripts/sun24/gen_lean.py`.

## Status

- Not found in OEIS or on the web (searched 2026-11-02).
- Formalised in Lean (2026-11-03).
