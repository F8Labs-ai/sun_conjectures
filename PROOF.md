# Proofs of Sun's Conjectures 2.7(i) and 2.14(ii), and a counterexample to Conjecture 2.1

Sections 0–3 concern the two proofs; Section 4 the counterexample.

Notation: π(x) is the number of primes ≤ x; log is the natural logarithm. References are to
Z.-W. Sun, *Problems on combinatorial properties of primes*, arXiv:1402.6641. The Lean files formalize exactly
the arguments below.

## 0. The common reduction

**Lemma 0.** Let k ≥ 0 and A, B > 0 be real numbers. If k(B − A) < A log A, then k log B < (k + 1) log A,
i.e. B^k < A^{k+1}.

*Proof.* log(B/A) ≤ B/A − 1, so A(log B − log A) ≤ B − A. Multiply by k ≥ 0:
A·k(log B − log A) ≤ k(B − A) < A log A. Divide by A. ∎

Both conjectures have the form a_{k+1}^{1/(k+1)} < a_k^{1/k}, which is a_{k+1}^k < a_k^{k+1}. So it is enough
to show

    k · (a_{k+1} − a_k) < a_k · log a_k.                                          (*)

The left side needs an **upper** bound for the number of primes in a short interval. The right side needs a
**lower** bound for π(x) on average. Both are elementary.

## 1. Conjecture 2.7(i): π(kn)^{1/k} is strictly decreasing in k (n ≥ 5)

**Theorem.** For all integers n ≥ 5 and k ≥ 1, π((k+1)n)^{1/(k+1)} < π(kn)^{1/k}.

Put A = π(kn), B = π((k+1)n), m = kn.

**Step 1 (short intervals, mod 6).** For x ≥ 7 and n ≥ 5, π(x + n) − π(x) ≤ 4n/9.
Every prime p > 3 satisfies p ≡ ±1 (mod 6). An interval of n consecutive integers contains at most
2(⌊n/6⌋ + 1) such numbers. For n ≥ 18 this is ≤ 4n/9. For 5 ≤ n < 18 the bound is checked for each residue
of x mod 6 directly (`small_residue_count`).

Hence k(B − A) ≤ (4/9)kn = (4/9)m.

**Step 2 (Chebyshev).** For m ≥ 7, (4/9)m < π(m) log π(m).
* For m ≥ 4096: Chebyshev's elementary bound ψ(m) ≥ m log 2 − log(m + 1) together with ψ(m) ≤ π(m) log m
  gives π(m) ≥ (m log 2 − log(m+1))/log m. Then π(m) log π(m) ≥ (4/9)m follows by elementary estimates
  (log 2 = 0.693… is comfortably larger than 4/9 after the log log m correction).
* For 7 ≤ m < 4096: on each of a few ranges [l, u], a lower bound π(l) ≥ a ≥ 2^b with 400u < 621ab implies the
  inequality on the whole range (`checkpoint`); the values π(l) are computed by the kernel.

**Step 3.** If kn ≥ 17, Steps 1 and 2 give k(B − A) ≤ (4/9)m < A log A, and Lemma 0 finishes the proof.
The finitely many cases with kn < 17 (n ≤ 16, k ≤ 3) are checked directly. ∎

## 2. Conjecture 2.14(ii): π(n²)^{1/n} is strictly decreasing (n ≥ 3)

**Theorem.** For every integer n ≥ 3, π((n+1)²)^{1/(n+1)} < π(n²)^{1/n}.

Put A = π(n²), B = π((n+1)²), so B − A counts the primes in (n², (n+1)²], an interval of length 2n + 1. By (*)
we need n(B − A) < A log A.

**Case n ≥ 1000 (analytic).**
* *Wheel mod 210.* φ(210) = 48, so B − A ≤ 48(⌊(2n+1)/210⌋ + 1), and n(B − A) ≤ 0.506 n² for n ≥ 1000.
* *Chebyshev.* Mathlib's `Chebyshev.pi_ge_of_four_le` gives π(x) ≥ x log 2 / log x. With x = n² ≥ 2^19 and
  t = log x one gets log A ≥ (15/16)t − 2.2155, hence A log A ≥ 0.533 n².

Since 0.506 < 0.533, (*) holds.

**Case 3 ≤ n < 1000 (computation).** A checker `chk` walks through a table of the values π(n²) and verifies for
each n that
1. the difference of consecutive table entries equals the number of primes in (n², (n+1)²], and
2. the integer inequality π((n+1)²)ⁿ < π(n²)ⁿ⁺¹ holds.

Its soundness is proved in Lean (`chk_sound`, `chk_last`). For n ≥ 32 the primes in (n², (n+1)²] ⊂ (1000, 10⁶]
are counted as the integers coprime to 1000!, which is equivalent there and much faster for the kernel. The
table is split into 33 chunks so that the kernel check fits in memory. ∎

## 3. Why these conjectures are easy, and the general principle

In both cases the ratio (right side)/(left side) of (*) grows like log n, so crude sieve bounds suffice. The
same argument proves:

> Let g: ℕ → ℕ grow polynomially, in the sense that k(g(k+1) − g(k)) ≤ M·g(k) for some M and all large k.
> Then π(g(k))^{1/k} is eventually strictly decreasing.

Choose a modulus q with φ(q)/q < (log 2)/M, which exists because ∏(1 − 1/p) → 0. The wheel mod q bounds the
left side of (*) by about M·(φ(q)/q)·g(k), and Chebyshev bounds the right side below by about (log 2)·g(k).

The principle stops at exponential growth: π(2^k)^{1/k} increases to 2.

By contrast, conjectures such as Firoozbakht's (p_n^{1/n} decreasing) or Legendre's (a prime between n² and
(n+1)²) need **lower** bounds for primes in short intervals, which are far beyond these methods.

## 4. Counterexample to Conjecture 2.1 of arXiv:1208.2683

Here p_k is the k-th prime. Sun's Conjecture 2.1 (Z.-W. Sun, *Conjectures involving arithmetical sequences*,
arXiv:1208.2683) states: for every real α > 0,

    (1/n) Σ_{k=1}^{n} p_k^α < p_n^α / (α + 1)    for all n ≥ 2⌈α⌉² + ⌈α⌉ + 6.

For α = 1 this is Mandl's inequality Σ_{k ≤ n} p_k < n p_n / 2 (n ≥ 9), proved by Dusart. The right side is
what the left side would be if the primes were spread evenly, since (1/x)∫₀ˣ t^α dt = x^α/(α + 1).

**Theorem.** The conjecture fails for α = 46, n = 4447.

*Proof.* ⌈46⌉ = 46, so the threshold is 2·46² + 46 + 6 = 4284 ≤ 4447. Multiplying the claimed inequality by
47n, it would say 47 Σ_{k ≤ 4447} p_k^46 < 4447 · p_4447^46. We have p_4447 = 42499 and, computing exactly in
integers,

    47 Σ_{k=1}^{4447} p_k^46 ≥ 4447 · 42499^46,

the ratio of the two sides being about 1.0000512. ∎

**How the kernel checks it.** The first 4448 primes all lie below 42849 = 207². Below 207 primality is decided
directly; on [207, 42849) a number is prime iff it is coprime to 206!, since a composite number below 207² has a
prime factor ≤ 206. With this test the kernel counts the primes below 42499 and 42509 (4446 and 4447), which
identifies p_4447 = 42499 and p_4448 = 42509, and evaluates the sum of the 46th powers exactly
(`blk`, `blk_spec`, `blk_ineq`). Since the argument uses n ≥ threshold only through 4284 < 4447, it also refutes
the journal version with n > threshold.

**Remarks.** The violation is driven by a cluster of primes just below p_4447 (…, 42473, 42487, 42491, 42499,
with gaps 14, 4, 8), which makes the sum large relative to p_4447. For real α it occurs only in a thin window
just below α = 46: for α slightly above 46, ⌈α⌉ = 47 raises the threshold to 4471 > 4447. An exact search over
integer α ≤ 80 and n ≤ 30000 finds no other violation.
