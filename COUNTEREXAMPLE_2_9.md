# A counterexample to Sun's Conjecture 2.9 (arXiv:1208.2683): E(x, x+4, x+6) ≠ ∅

**Statement (Sun, 2012-08-20).** Let q_1 < q_2 < … be the positive integers x with x, x+4 and x+6 all prime.
Sun defines E(x, x+4, x+6) as the set of n for which ⁿ√q_n > ⁿ⁺¹√q_{n+1} fails, i.e. q_{n+1} ≥ q_n^{1+1/n}.
He conjectures that E(x, x+4, x+6) = ∅, and also that E(x, x+2, x+6) = ∅.

**Counterexample.** n = 77 055:

    q_n     = 148 770 907        (148770907, 148770911, 148770913 are prime)
    q_{n+1} = 148 809 247        (148809247, 148809251, 148809253 are prime)
    gap 38 340, with no admissible x strictly in between
    n · log(q_{n+1}/q_n) = 19.85541493…  >  log q_n = 18.81791814…,   r = 1.0551334…

So 77 055 ∈ E(x, x+4, x+6). Sun's search must have stopped below 1.49·10⁸.

## Verification

1. `tuples_firoz.c` (C, segmented sieve) scans to 10¹¹. In that range 77 055 is the *only* element of
   E(x, x+4, x+6). A debug build that prints the failing pair gives the values above.
2. `verify_tuple.py` (Python) checks it independently:
   - a numpy sieve of Eratosthenes recounts the triples and gives n = 77 055 and the next one;
   - sympy `isprime` confirms the six primes and that no x in (q_n, q_{n+1}) qualifies;
   - the comparison is done with 60-digit mpmath arithmetic.

## Other tuple claims, to 10¹¹

| family | count to 10¹¹ | E found | Sun's E | N₀ (found / Sun) |
|---|---|---|---|---|
| (x, x+2) | 224 376 048 | ∅ | ∅ | 4 / 4 |
| (x, x+2, x+6) | 20 093 124 | ∅ | ∅ | 3 / 3 |
| **(x, x+4, x+6)** | 20 081 601 | **{77 055}** | ∅ | 6 / 6 |
| (x, 2x+1) | 218 116 524 | {3, 4} | {3, 4} | 3 / 3 |
| (x, 2x−1) | 218 134 071 | {2, 3, 6} | {2, 3, 6} | 3 / 3 |

## Why it is possible

For a k-tuple family the allowed gap is mean·log q, while the typical largest gap is only mean·log #S ≈
mean·(log q − k log log q). Violations therefore need a large Poisson-type fluctuation of a single gap. The
expected number of them beyond X is ≍ 1/log^{k−1} X, which is finite, but not zero. This density heuristic
predicts finitely many exceptions; it does **not** predict that they are all small. This one
sits at 1.5·10⁸.

## Lean formalisation (`Sunproj/Triple/`)

`Sun29.lean` proves `Triple.sun29_false : ¬ SunConj29`. The definitions:
- `IsT x := x.Prime ∧ (x+4).Prime ∧ (x+6).Prime`;
- `q n := Nat.nth IsT (n - 1)`;
- `SunConj29 := ∀ n ≥ 1, q(n+1) < q(n)^(1+1/n)` in ℝ.

`sun29_counterexample` gives an n ≥ 77 055 with q(n) = 148 770 907, q(n+1) = 148 809 247 and
148770907^(1+1/n) < 148809247.

As for 2.4(ii), only a *lower* bound on n is certified, since the inequality fails for every n ≥ 73 029.

| file | content |
|---|---|
| `Checker.lean` | `run`: members, each with three Lucas certificates (`PrimRoot.certPrime`, reused from the 2.4 proof); `runGap`: one divisor 2 ≤ d < x of x, x+4 or x+6 per integer; soundness `run_sound`, `runGap_sound` |
| `Data/T000–T102.lean` | the 77 055 triples, 231 165 Lucas certificates, 1.6M tokens, `decide +kernel` |
| `Count.lean` | chains the chunks: `77055 ≤ Nat.count IsT 148770908` |
| `Gap.lean` | q_n and q_{n+1} are members; the 38 339 integers in between are not (4 parts) |
| `Sun29.lean` | Nat.nth bookkeeping; kernel check 148770907^77056 < 148809247^77055; passage to ℝ |

**Trust base.** There is no `sorry` and no `native_decide`; the axioms are propext, Classical.choice and
Quot.sound. Generator: `scripts/sun29/gen29.py`. It contains a Python model of the checker, which runs on every
chunk before the Lean files are written.

## Status

- Literature and OEIS searched 2026-11-03; see below.

## Literature (searched 2026-11-03)

**The gap itself is known.** 148 770 907 → 148 809 247 (gap 38 340) is the 38th record gap between triples
(p, p+4, p+6):
- OEIS A201596 / A201597 (A. Kourbatov);
- Kourbatov, *Tables of record gaps between prime constellations*, arXiv:1309.4053 (Sept 2013), Table 3.2.

That table was public before the final version of Sun's paper (v9, Oct 2013), which still states
E(x, x+4, x+6) = ∅.

**The link to Sun's conjecture is not made anywhere we found.**
- OEIS has no hits for 148770907 or 148809247 outside the record-gap entries, and none citing 1208.2683.
- Web search finds nothing on Conjecture 2.9 being false.
- Kourbatov & Wolf, *Predicting maximal gaps in sets of primes*, arXiv:1901.03785 (2019), cite this paper
  of Sun's only for Conj. 2.3 (APs), not for the tuple conjectures.

**Beyond 10¹¹ (estimate).** Kourbatov's tables give the record gaps up to 5.4·10¹⁴ for (x, x+4, x+6) and
6.7·10¹⁴ for (x, x+2, x+6). Only a record gap can plausibly violate the inequality, because n/(q log q)
decreases. We computed r for each record, with n estimated by C·∫dt/log³t (C fitted to the exact counts at
10¹¹):
- (x, x+4, x+6): max r ≈ 1.055 at our counterexample; the next are 0.957 (p = 715 873) and 0.918
  (p = 5.4·10¹⁴).
- (x, x+2, x+6): max r ≈ 0.892 (p = 7.27·10⁹).

So 77 055 is very probably the only element of E(x, x+4, x+6) below 5·10¹⁴, and E(x, x+2, x+6) = ∅ there.
This is an estimate, not a proof.
- Formalised in Lean (2026-11-03).
