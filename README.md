# Five of Zhi-Wei Sun's conjectures on primes, settled in Lean 4

Machine-checked results on five conjectures of Zhi-Wei Sun:

* **two proved**: Conjectures 2.7(i) and 2.14(ii) from
  Z.-W. Sun, *Problems on combinatorial properties of primes*, arXiv:1402.6641 (v12);
* **three disproved** by explicit counterexamples: Conjectures 2.1 (a generalized Mandl inequality), 2.4(ii)
  (largest negative primitive roots) and 2.9 (prime triples x, x+4, x+6) from
  Z.-W. Sun, *Conjectures involving arithmetical sequences*, arXiv:1208.2683 (v9).

| conjecture | result | main theorem | file |
|---|---|---|---|
| 2.7(i) | proved | `SunComplete.sun_roots` | `SunConjectures/SunComplete.lean` |
| 2.14(ii) | proved | `SunSquares.sun_sq_roots` | `SunConjectures/SunSquares.lean` |
| 2.1 | disproved: α = 46, n = 4447 | `SunMandl.not_conjecture` | `SunConjectures/SunMandl.lean` |
| 2.4(ii) | disproved: a = −3, n = 754 589 | `PrimRoot.sun24ii_false` | `Sunproj/PrimRoot/Sun24.lean` |
| 2.9 | disproved: n = 77 055 | `Triple.sun29_false` | `Sunproj/Triple/Sun29.lean` |

All results are unconditional: no `sorry`, no `axiom`, no `native_decide`, no external hypotheses.
`#print axioms` reports only Lean's standard `propext`, `Classical.choice`, `Quot.sound`.

## Proved statements

**Conjecture 2.7(i)**, file `SunConjectures/SunComplete.lean`

```lean
theorem SunComplete.sun_roots (n k : ℕ) (hn : 5 ≤ n) (hk : 1 ≤ k) :
    (π((k + 1) * n) : ℝ) ^ (1 / ((k : ℝ) + 1)) < (π(k * n) : ℝ) ^ (1 / (k : ℝ))
```

That is, π(kn)^{1/k} is strictly decreasing in k for every n ≥ 5. Sun states it for k ≤ n; the restriction is
not needed. The bound n ≥ 5 is sharp: the inequality fails for n = 4.

**Conjecture 2.14(ii)**, file `SunConjectures/SunSquares.lean`

```lean
theorem SunSquares.sun_sq_roots (n : ℕ) (hn : 3 ≤ n) :
    (π((n + 1) ^ 2) : ℝ) ^ (1 / ((n : ℝ) + 1)) < (π(n ^ 2) : ℝ) ^ (1 / (n : ℝ))
```

That is, π(n²)^{1/n} is strictly decreasing for n ≥ 3.

Both files also contain the integer-power forms `sun_power` and `sun_sq_power`, e.g.
π((n+1)²)ⁿ < π(n²)ⁿ⁺¹. In Lean, π is `Nat.primeCounting`.

## Disproved statements

### Conjecture 2.1: generalized Mandl inequality

**Conjecture 2.1** of arXiv:1208.2683, file `SunConjectures/SunMandl.lean`. Sun conjectured that for every real
α > 0

    (1/n) · Σ_{k=1}^{n} p_k^α  <  p_n^α / (α + 1)    for all n ≥ 2⌈α⌉² + ⌈α⌉ + 6,

where p_k is the k-th prime. For α = 1 this is Mandl's inequality. It fails for **α = 46, n = 4447**: the
threshold is 4284, p₄₄₄₇ = 42499, and

    47 · Σ_{k=1}^{4447} p_k^46  ≥  4447 · 42499^46.

```lean
theorem SunMandl.not_conjecture : ¬ SunMandl.Conjecture
theorem SunMandl.not_conjecturePublished : ¬ SunMandl.ConjecturePublished
```

`Conjecture` is the arXiv statement (n ≥ threshold); `ConjecturePublished` is the weaker journal version
(n > threshold). The violation is small: the left side exceeds the right by a factor of about 1.0000512.
Sun's remark after the conjecture reports a numerical check for α = 2, …, 700 and n ≤ 10⁶; this case lies inside
that range. An exact integer search over α = 1, …, 80 and n ≤ 30000 finds no other violation.

### Conjecture 2.4(ii): largest negative primitive roots

Let a < 0 be an integer that is not a perfect power, and let p₁(a) < p₂(a) < … be the primes p for which a is the
largest negative primitive root mod p: a is a primitive root mod p and no b with a < b < 0 is one. Sun conjectured
p_{n+1}(a) < p_n(a)^{1+1/n} for all n ≥ 1, "with the only exception a = −2 and n = 13". It fails for
**a = −3, n = 754 589**:

    p_n = 51 459 203,   p_{n+1} = 51 460 433,   p_n^{1+1/n} ≈ 51 460 413.9 < p_{n+1}.

```lean
theorem PrimRoot.sun24ii_false : ¬ PrimRoot.SunConj24ii
```

Write-up: [COUNTEREXAMPLE_2_4.md](COUNTEREXAMPLE_2_4.md).

### Conjecture 2.9: prime triples (x, x+4, x+6)

Let q₁ < q₂ < … be the positive integers x with x, x+4, x+6 all prime. Sun conjectured E(x, x+4, x+6) = ∅,
i.e. q_{n+1} < q_n^{1+1/n} for all n ≥ 1. It fails for **n = 77 055**:

    q_n = 148 770 907,   q_{n+1} = 148 809 247,   q_n^{1+1/n} ≈ 148 807 243.4 < q_{n+1}.

```lean
theorem Triple.sun29_false : ¬ Triple.SunConj29
```

Write-up: [COUNTEREXAMPLE_2_9.md](COUNTEREXAMPLE_2_9.md).

**How 2.4(ii) and 2.9 are checked.** For both, Lean proves that the two consecutive terms are members of the
sequence, that nothing in between is, and that the index is at least 754 589 (resp. 77 055). A lower bound on the
index suffices, because the inequality fails for every n ≥ 742 875 (resp. n ≥ 73 029). Membership is certified by
Lucas certificates (and, for 2.4(ii), a witness that −2 is not a primitive root), read by checkers whose soundness
is proved in `Sunproj/*/Checker.lean`. The data (754 589 and 77 055 members) is in `Sunproj/*/Data/`; the search
programs, independent checks and data generators are in `scripts/`.

## Build

Requires [elan](https://github.com/leanprover/elan). Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2`.

```bash
lake exe cache get
lake build           # 2.7(i), 2.14(ii), 2.1: a few minutes
lake build Sunproj   # 2.4(ii), 2.9: about 30 min of kernel time, about 13 GB of build output
```

The build prints the `#print axioms` output for the main theorems. `SunSquares.lean` takes about a minute and
roughly 4.5 GB of memory, because the kernel checks a table of π(n²) for n < 1000. `SunMandl.lean` takes about a
minute and 4 GB, because the kernel sums p_k^46 over the first 4447 primes.

`Sunproj` is not a default target, and GitHub CI builds only the default target, because the certificates for
2.4(ii) and 2.9 exceed the disk of a standard runner. `scripts/*/build_all.sh` builds their data chunks in batches
with a progress line.

## How the proofs work

A human-readable account of 2.7(i), 2.14(ii) and 2.1 is in [PROOF.md](PROOF.md); 2.4(ii) and 2.9 have their own
write-ups (linked above). For the two proofs, in short:

* a^{1/k} decreasing is equivalent to k·(π(next) − π(current)) < π(current)·log π(current);
* the left side is bounded by a wheel sieve (mod 6, resp. mod 210): few primes in a short interval;
* the right side is bounded by Chebyshev's elementary lower bound, which is already in Mathlib;
* the remaining finite range is checked by computation in the Lean kernel.

The inequalities have slack of order log n, which is why these elementary tools suffice.

The counterexample to 2.1 is a finite computation: the kernel certifies the first 4448 primes (below 207
directly, above as the numbers coprime to 206!) and evaluates the sum exactly in natural numbers.

## Status and novelty

We could not find an earlier proof of Conjecture 2.7(i) or 2.14(ii), or an earlier counterexample to
Conjecture 2.1, 2.4(ii) or 2.9: not in Sun's papers, his OEIS comments, google-deepmind/formal-conjectures, or
MathOverflow. Chinese-language journals and MathSciNet/zbMATH were not searched. If you know of earlier work,
please open an issue.

For 2.9 the gap itself is known: 148 770 907 → 148 809 247 is a record gap between prime triples (p, p+4, p+6)
(OEIS A201596; A. Kourbatov, arXiv:1309.4053, 2013). We found no source that connects it to Sun's conjecture.

The mathematics is elementary (Chebyshev-type bounds, sieving, primality certificates, finite computation). The
contribution is settling five items from Sun's lists, with every step checked by the Lean kernel.

## Credits

Developed with AI assistance from Claude (Anthropic) and ChatGPT Astra (OpenAI). The correctness of the results
does not rely on trusting either system: every step is checked by the Lean kernel.

## License

Apache License 2.0, see [LICENSE](LICENSE). This matches Lean and Mathlib.
