import Mathlib

/-!
# A counterexample to Z.-W. Sun's Conjecture 2.1 (generalized Mandl inequality)

Z.-W. Sun, *Conjectures involving arithmetical sequences*, Number Theory: Arithmetic in Shangri-La
(World Sci., 2013), 244–258, arXiv:1208.2683, Conjecture 2.1:
for every `α > 0`,

  `(1/n) ∑_{k=1}^{n} p_k ^ α < p_n ^ α / (α + 1)`  for all `n ≥ 2⌈α⌉² + ⌈α⌉ + 6`

(the published version has `n > 2⌈α⌉² + ⌈α⌉ + 6`).  Here `p_k` is the `k`-th prime, which is
`Nat.nth Nat.Prime (k - 1)` in Mathlib.

Both versions fail for `α = 46`, `n = 4447` (threshold `4284`, `p_4447 = 42499`):
`47 · ∑_{k ≤ 4447} p_k ^ 46 ≥ 4447 · 42499 ^ 46`.

The first 4448 primes are certified by the kernel: below `207` with Mathlib's decision procedure,
and on `[207, 42849)` as the numbers coprime to `206!` (a composite number below `207²` has a
prime factor `≤ 206`).
-/

namespace SunMandl

/-- Sun's Conjecture 2.1 as stated in arXiv:1208.2683 (`n ≥` threshold). -/
def Conjecture : Prop :=
  ∀ α : ℝ, 0 < α → ∀ n : ℕ, 2 * ⌈α⌉₊ ^ 2 + ⌈α⌉₊ + 6 ≤ n →
    (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, ((Nat.nth Nat.Prime k : ℕ) : ℝ) ^ α <
      ((Nat.nth Nat.Prime (n - 1) : ℕ) : ℝ) ^ α / (α + 1)

/-- The published version (`n >` threshold); it claims less. -/
def ConjecturePublished : Prop :=
  ∀ α : ℝ, 0 < α → ∀ n : ℕ, 2 * ⌈α⌉₊ ^ 2 + ⌈α⌉₊ + 6 < n →
    (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, ((Nat.nth Nat.Prime k : ℕ) : ℝ) ^ α <
      ((Nat.nth Nat.Prime (n - 1) : ℕ) : ℝ) ^ α / (α + 1)

/-! ### Sums over the first `m` primes -/

lemma sum_nth_prime (f : ℕ → ℕ) (m : ℕ) :
    ∑ k ∈ Finset.range m, f (Nat.nth Nat.Prime k) =
      ∑ j ∈ (Finset.range (Nat.nth Nat.Prime m)).filter Nat.Prime, f j := by
  induction m with
  | zero =>
    have h : (Finset.range (Nat.nth Nat.Prime 0)).filter Nat.Prime = ∅ := by
      rw [← Finset.card_eq_zero, ← Nat.count_eq_card_filter_range]
      exact Nat.count_nth_zero _
    rw [Finset.range_zero, Finset.sum_empty, h, Finset.sum_empty]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih,
      Nat.filter_range_nth_eq_insert_of_infinite Nat.infinite_setOfPred_prime m,
      Finset.sum_insert (by simp), add_comm]

/-! ### Kernel-checked primality on `[0, 42849)` -/

/-- `206!` as a literal, so that the kernel reads it instead of recomputing it. -/
def G : ℕ := 55999397401181624007970525662228881095168659729947683663459568612877337687103244532741481446193158669223111681827099783995223685855991394533857968704451505138207572405603545223305877760386469231760852842439470446554717967072798418218925958492128260636540143129576946167209039675309828823599001441864639500011288693462578636098658615322214400000000000000000000000000000000000000000000000000

lemma G_eq : G = Nat.factorial 206 := by decide +kernel

lemma coprime_G_iff (j : ℕ) (h1 : 206 < j) (h2 : j < 42849) :
    Nat.Coprime j G ↔ Nat.Prime j := by
  constructor
  · intro hc
    by_contra hp
    have hsq := Nat.minFac_sq_le_self (by omega) hp
    have hmf : Nat.minFac j ≤ 206 := by nlinarith
    have hd : Nat.minFac j ∣ G := G_eq ▸ Nat.dvd_factorial (Nat.minFac_pos j) hmf
    have h1' : Nat.minFac j = 1 := by
      have hg := Nat.dvd_gcd (Nat.minFac_dvd j) hd
      rwa [Nat.Coprime.gcd_eq_one hc, Nat.dvd_one] at hg
    rw [Nat.minFac_eq_one_iff] at h1'
    omega
  · intro hp
    have hnd : ¬ j ∣ Nat.factorial 206 := by rw [hp.dvd_factorial]; omega
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 (G_eq ▸ hnd)

/-- Primality test used by the kernel. -/
def isP (j : ℕ) : Bool :=
  if j < 207 then decide (Nat.Prime j) else Nat.gcd j G == 1

lemma isP_iff (j : ℕ) (hj : j < 42849) : isP j = true ↔ Nat.Prime j := by
  unfold isP
  split_ifs with h
  · exact decide_eq_true_iff
  · rw [beq_iff_eq]
    exact coprime_G_iff j (by omega) hj

/-- `∑_{a ≤ j < a + len, j prime} j ^ 46` and the number of such `j`, computed with `isP`. -/
def blk (a : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | len + 1 =>
    let r := blk a len
    if isP (a + len) then (r.1 + (a + len) ^ 46, r.2 + 1) else r

lemma blk_spec (a len : ℕ) (h : a + len ≤ 42849) :
    blk a len = (∑ j ∈ Finset.Ico a (a + len) with Nat.Prime j, j ^ 46,
      (Finset.filter Nat.Prime (Finset.Ico a (a + len))).card) := by
  induction len with
  | zero => simp [blk]
  | succ len ih =>
    have ih := ih (by omega)
    have hP := isP_iff (a + len) (by omega)
    rw [show a + (len + 1) = (a + len) + 1 by ring, ← Finset.insert_Ico_right_eq_Ico_add_one (by omega),
      Finset.filter_insert, blk]
    by_cases hp : Nat.Prime (a + len)
    · have hn : a + len ∉ Finset.filter Nat.Prime (Finset.Ico a (a + len)) := by simp
      simp only [hP.2 hp, ite_true, hp, ih, Finset.sum_insert hn, Finset.card_insert_of_notMem hn]
      exact Prod.ext (add_comm _ _) rfl
    · have hq : isP (a + len) = false := by
        cases h' : isP (a + len)
        · rfl
        · exact absurd (hP.1 h') hp
      simp only [hq, hp, ite_false, Bool.false_eq_true, ih]

/-! ### The kernel computation -/

lemma blk_42509_count : (blk 0 42509).2 = 4447 := by decide +kernel

lemma blk_42499_count : (blk 0 42499).2 = 4446 := by decide +kernel

/-- The counterexample, as an inequality between natural numbers. -/
lemma blk_ineq : 4447 * 42499 ^ 46 ≤ 47 * (blk 0 42509).1 := by decide +kernel

lemma prime_42509 : Nat.Prime 42509 := (isP_iff 42509 (by norm_num)).1 (by decide +kernel)

lemma prime_42499 : Nat.Prime 42499 := (isP_iff 42499 (by norm_num)).1 (by decide +kernel)

lemma count_eq_blk (N : ℕ) (hN : N ≤ 42849) : Nat.count Nat.Prime N = (blk 0 N).2 := by
  rw [Nat.count_eq_card_filter_range, blk_spec 0 N (by omega), Finset.range_eq_Ico, zero_add]

/-- `p_4448 = 42509`. -/
lemma nth_4447 : Nat.nth Nat.Prime 4447 = 42509 := by
  have h := Nat.nth_count prime_42509
  rwa [count_eq_blk 42509 (by norm_num), blk_42509_count] at h

/-- `p_4447 = 42499`. -/
lemma nth_4446 : Nat.nth Nat.Prime 4446 = 42499 := by
  have h := Nat.nth_count prime_42499
  rwa [count_eq_blk 42499 (by norm_num), blk_42499_count] at h

/-- `∑_{k ≤ 4447} p_k ^ 46 = (blk 0 42509).1`. -/
lemma sum_first_4447 : ∑ k ∈ Finset.range 4447, (Nat.nth Nat.Prime k) ^ 46 = (blk 0 42509).1 := by
  rw [sum_nth_prime (fun j => j ^ 46) 4447, nth_4447, blk_spec 0 42509 (by norm_num),
    Finset.range_eq_Ico, zero_add]

/-! ### Main results -/

/-- Sun's Conjecture 2.1, in its published form (`n > 2⌈α⌉² + ⌈α⌉ + 6`), is false:
`α = 46`, `n = 4447`. -/
theorem not_conjecturePublished : ¬ ConjecturePublished := by
  intro h
  have hc : ⌈(46 : ℝ)⌉₊ = 46 := Nat.ceil_ofNat 46
  have h1 := h 46 (by norm_num) 4447 (by rw [hc]; norm_num)
  have hpow : ∀ x : ℝ, x ^ (46 : ℝ) = x ^ (46 : ℕ) := fun x => by
    exact_mod_cast Real.rpow_natCast x 46
  simp only [hpow] at h1
  rw [show 4447 - 1 = 4446 from rfl, nth_4446] at h1
  have hsum : ∑ k ∈ Finset.range 4447, ((Nat.nth Nat.Prime k : ℕ) : ℝ) ^ 46 =
      ((blk 0 42509).1 : ℝ) := by
    rw [← sum_first_4447]; push_cast; rfl
  rw [hsum] at h1
  have key : (4447 : ℝ) * (42499 : ℝ) ^ 46 ≤ 47 * ((blk 0 42509).1 : ℝ) := by
    exact_mod_cast blk_ineq
  generalize ((blk 0 42509).1 : ℝ) = S at h1 key
  generalize (42499 : ℝ) ^ 46 = P at h1 key
  push_cast at h1
  linarith

/-- Sun's Conjecture 2.1 as stated in arXiv:1208.2683 (`n ≥ 2⌈α⌉² + ⌈α⌉ + 6`) is false. -/
theorem not_conjecture : ¬ Conjecture := fun h =>
  not_conjecturePublished fun α hα n hn => h α hα n hn.le

end SunMandl

#print axioms SunMandl.not_conjecture
#print axioms SunMandl.not_conjecturePublished
