# Three of Zhi-Wei Sun's conjectures on primes, settled in Lean 4

Machine-checked results on three conjectures of Zhi-Wei Sun:

* **two proved**: Conjectures 2.7(i) and 2.14(ii) from
  Z.-W. Sun, *Problems on combinatorial properties of primes*, arXiv:1402.6641 (v12);
* **one disproved**: Conjecture 2.1 (a generalized Mandl inequality) from
  Z.-W. Sun, *Conjectures involving arithmetical sequences*, arXiv:1208.2683, by an explicit counterexample.

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

## Disproved statement

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

## Build

Requires [elan](https://github.com/leanprover/elan). Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2`.

```bash
lake exe cache get
lake build
```

The build prints the `#print axioms` output for the main theorems. `SunSquares.lean` takes about a minute and
roughly 4.5 GB of memory, because the kernel checks a table of π(n²) for n < 1000. `SunMandl.lean` takes about a
minute and 4 GB, because the kernel sums p_k^46 over the first 4447 primes.

## How the proofs work

A human-readable account of all three results is in [PROOF.md](PROOF.md). For the two proofs, in short:

* a^{1/k} decreasing is equivalent to k·(π(next) − π(current)) < π(current)·log π(current);
* the left side is bounded by a wheel sieve (mod 6, resp. mod 210): few primes in a short interval;
* the right side is bounded by Chebyshev's elementary lower bound, which is already in Mathlib;
* the remaining finite range is checked by computation in the Lean kernel.

The inequalities have slack of order log n, which is why these elementary tools suffice.

The counterexample is a finite computation: the kernel certifies the first 4448 primes (below 207 directly,
above as the numbers coprime to 206!) and evaluates the sum exactly in natural numbers.

## Status and novelty

We could not find an earlier proof of Conjecture 2.7(i) or 2.14(ii), or an earlier counterexample to
Conjecture 2.1: not in Sun's papers, his OEIS comments, google-deepmind/formal-conjectures, or MathOverflow.
Chinese-language journals and MathSciNet/zbMATH were not searched. If you know of earlier work, please open an
issue.

The mathematics is elementary (Chebyshev-type bounds, sieving, finite computation). The contribution is settling
three items from Sun's lists, with every step checked by the Lean kernel.

## Credits

Developed with AI assistance from Claude (Anthropic) and ChatGPT Astra (OpenAI). The correctness of the results
does not rely on trusting either system: every step is checked by the Lean kernel.

## License

Apache License 2.0, see [LICENSE](LICENSE). This matches Lean and Mathlib.
