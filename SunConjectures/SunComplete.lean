import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
An unconditional proof of Sun's prime-counting root inequality.
The analytic input is Mathlib's elementary Chebyshev bound, not an
assumed Rosser--Schoenfeld estimate. No external mathematical hypotheses.
-/

set_option autoImplicit false

namespace SunComplete

lemma prime_mod_six (p : ℕ) (hp : p.Prime) (hlarge : 3 < p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 := hp.eq_two_or_odd
  have h3 : p % 3 ≠ 0 := by
    intro h
    have := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h)
    omega
  omega

lemma small_residue_count (r n : ℕ) (hr : r < 6) (hn : 5 ≤ n) (hn' : n < 18) :
    9 * Nat.count (fun j => (r + 1 + j) % 6 = 1 ∨ (r + 1 + j) % 6 = 5) n ≤ 4 * n := by
  interval_cases r <;> interval_cases n <;> decide

lemma pc_interval_four_ninths (x n : ℕ) (hx : 7 ≤ x) (hn : 5 ≤ n) :
    9 * (Nat.primeCounting (x + n) - Nat.primeCounting x) ≤ 4 * n := by
  by_cases hn' : 18 ≤ n
  · have h := Nat.primeCounting'_add_le (a := 6) (k := x + 1)
      (by decide +kernel) (by omega) n
    have heq : x + 1 + n = x + n + 1 := by omega
    rw [heq] at h
    change Nat.primeCounting (x + n) ≤ Nat.primeCounting x +
      Nat.totient 6 * (n / 6 + 1) at h
    rw [show Nat.totient 6 = 2 by decide] at h
    omega
  · have hcount : Nat.count (fun j => Nat.Prime (x + 1 + j)) n ≤
        Nat.count (fun j => (x % 6 + 1 + j) % 6 = 1 ∨
          (x % 6 + 1 + j) % 6 = 5) n := by
      apply Nat.count_mono_left
      intro j hj hp
      have h := prime_mod_six (x + 1 + j) hp (by omega)
      simpa only [Nat.add_mod, Nat.mod_mod] using h
    have htable := small_residue_count (x % 6) n (Nat.mod_lt _ (by decide +kernel)) hn (by omega)
    have heq : Nat.primeCounting (x + n) = Nat.primeCounting x +
        Nat.count (fun j => Nat.Prime (x + 1 + j)) n := by
      unfold Nat.primeCounting Nat.primeCounting'
      have h : x + n + 1 = (x + 1) + n := by omega
      rw [h, Nat.count_add]
    omega

lemma chebyshev_lower (m : ℕ) :
    (m : ℝ) * Real.log 2 - Real.log ((m : ℝ) + 1) ≤
      (Nat.primeCounting m : ℝ) * Real.log m := by
  exact (Chebyshev.psi_ge m).trans (Chebyshev.psi_le_primeCounting_mul_log m)

lemma log_small_correction (x : ℝ) (hx : 4096 ≤ x) :
    Real.log (x + 1) < x / 50 := by
  have ht := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / 256 by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at ht
  have hlog256 : Real.log (256 : ℝ) < 8 := by
    have h : Real.log ((2 : ℝ) ^ 8) = 8 * Real.log 2 := by rw [Real.log_pow]; norm_num
    norm_num only [show (2 : ℝ)^8 = 256 by norm_num] at h
    linarith [Real.log_two_lt_d9]
  linarith

lemma large_log_bound (m : ℕ) (hm : 4096 ≤ m) :
    (4 / 9 : ℝ) * m < (Nat.primeCounting m : ℝ) * Real.log (Nat.primeCounting m) := by
  let x : ℝ := m
  let A : ℝ := Nat.primeCounting m
  have hx : 4096 ≤ x := by dsimp [x]; exact_mod_cast hm
  have ht : 8 ≤ Real.log x := by
    have hmon := Real.log_le_log (by norm_num : (0 : ℝ) < 4096) hx
    have hpow : Real.log (4096 : ℝ) = 12 * Real.log 2 := by
      rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_gt_d9]
  have htpos : 0 < Real.log x := by linarith
  have hcheb : x * Real.log 2 - Real.log (x + 1) ≤ A * Real.log x := chebyshev_lower m
  have hcorr := log_small_correction x hx
  have hl2 : (69 / 100 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hAt : (2 / 3 : ℝ) * x < A * Real.log x := by
    nlinarith [mul_pos (show 0 < x by linarith) (sub_pos.mpr hl2)]
  have hA : 0 < A := by nlinarith
  have hdiv : (2 / 3 : ℝ) * x / Real.log x < A := (div_lt_iff₀ htpos).2 hAt
  have hlogA := Real.log_lt_log (show 0 < (2 / 3 : ℝ) * x / Real.log x by positivity) hdiv
  rw [Real.log_div (by positivity) (ne_of_gt htpos),
    Real.log_mul (by norm_num) (by positivity)] at hlogA
  have hc : -(1 / 2 : ℝ) ≤ Real.log (2 / 3 : ℝ) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 / 3 by norm_num)
    norm_num at this ⊢; exact this
  have hlog6 : Real.log (6 : ℝ) < 9 / 5 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]
  have htt := Real.log_le_sub_one_of_pos (show 0 < Real.log x / 6 by positivity)
  rw [Real.log_div (ne_of_gt htpos) (by norm_num)] at htt
  have hAlog : (2 / 3 : ℝ) * Real.log x < Real.log A := by linarith
  change (4 / 9 : ℝ) * x < A * Real.log A
  nlinarith [mul_pos hA (sub_pos.mpr hAlog)]

-- Each short block is evaluated by the Lean kernel, then composed by count_add.

private lemma count_to_0 : Nat.count Nat.Prime 0 = 0 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_0_8 :
    Nat.count (fun j => Nat.Prime (0 + j)) 8 = 4 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_8 : Nat.count Nat.Prime 8 = 4 := by
  rw [show 8 = 0 + 8 by decide, Nat.count_add, count_to_0, block_0_8]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_8_14 :
    Nat.count (fun j => Nat.Prime (8 + j)) 6 = 2 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_14 : Nat.count Nat.Prime 14 = 6 := by
  rw [show 14 = 8 + 6 by decide, Nat.count_add, count_to_8, block_8_14]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_14_20 :
    Nat.count (fun j => Nat.Prime (14 + j)) 6 = 2 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_20 : Nat.count Nat.Prime 20 = 8 := by
  rw [show 20 = 14 + 6 by decide, Nat.count_add, count_to_14, block_14_20]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_20_39 :
    Nat.count (fun j => Nat.Prime (20 + j)) 19 = 4 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_39 : Nat.count Nat.Prime 39 = 12 := by
  rw [show 39 = 20 + 19 by decide, Nat.count_add, count_to_20, block_20_39]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_39_57 :
    Nat.count (fun j => Nat.Prime (39 + j)) 18 = 4 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_57 : Nat.count Nat.Prime 57 = 16 := by
  rw [show 57 = 39 + 18 by decide, Nat.count_add, count_to_39, block_39_57]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_57_100 :
    Nat.count (fun j => Nat.Prime (57 + j)) 43 = 9 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_100 : Nat.count Nat.Prime 100 = 25 := by
  rw [show 100 = 57 + 43 by decide, Nat.count_add, count_to_57, block_57_100]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_100_101 :
    Nat.count (fun j => Nat.Prime (100 + j)) 1 = 0 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_101 : Nat.count Nat.Prime 101 = 25 := by
  rw [show 101 = 100 + 1 by decide, Nat.count_add, count_to_100, block_100_101]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_101_157 :
    Nat.count (fun j => Nat.Prime (101 + j)) 56 = 11 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_157 : Nat.count Nat.Prime 157 = 36 := by
  rw [show 157 = 101 + 56 by decide, Nat.count_add, count_to_101, block_101_157]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_157_200 :
    Nat.count (fun j => Nat.Prime (157 + j)) 43 = 10 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_200 : Nat.count Nat.Prime 200 = 46 := by
  rw [show 200 = 157 + 43 by decide, Nat.count_add, count_to_157, block_157_200]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_200_281 :
    Nat.count (fun j => Nat.Prime (200 + j)) 81 = 13 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_281 : Nat.count Nat.Prime 281 = 59 := by
  rw [show 281 = 200 + 81 by decide, Nat.count_add, count_to_200, block_200_281]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_281_300 :
    Nat.count (fun j => Nat.Prime (281 + j)) 19 = 3 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_300 : Nat.count Nat.Prime 300 = 62 := by
  rw [show 300 = 281 + 19 by decide, Nat.count_add, count_to_281, block_281_300]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_300_400 :
    Nat.count (fun j => Nat.Prime (300 + j)) 100 = 16 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_400 : Nat.count Nat.Prime 400 = 78 := by
  rw [show 400 = 300 + 100 by decide, Nat.count_add, count_to_300, block_300_400]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_400_459 :
    Nat.count (fun j => Nat.Prime (400 + j)) 59 = 10 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_459 : Nat.count Nat.Prime 459 = 88 := by
  rw [show 459 = 400 + 59 by decide, Nat.count_add, count_to_400, block_400_459]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_459_500 :
    Nat.count (fun j => Nat.Prime (459 + j)) 41 = 7 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_500 : Nat.count Nat.Prime 500 = 95 := by
  rw [show 500 = 459 + 41 by decide, Nat.count_add, count_to_459, block_459_500]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_500_600 :
    Nat.count (fun j => Nat.Prime (500 + j)) 100 = 14 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_600 : Nat.count Nat.Prime 600 = 109 := by
  rw [show 600 = 500 + 100 by decide, Nat.count_add, count_to_500, block_500_600]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_600_700 :
    Nat.count (fun j => Nat.Prime (600 + j)) 100 = 16 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_700 : Nat.count Nat.Prime 700 = 125 := by
  rw [show 700 = 600 + 100 by decide, Nat.count_add, count_to_600, block_600_700]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_700_800 :
    Nat.count (fun j => Nat.Prime (700 + j)) 100 = 14 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_800 : Nat.count Nat.Prime 800 = 139 := by
  rw [show 800 = 700 + 100 by decide, Nat.count_add, count_to_700, block_700_800]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_800_821 :
    Nat.count (fun j => Nat.Prime (800 + j)) 21 = 2 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_821 : Nat.count Nat.Prime 821 = 141 := by
  rw [show 821 = 800 + 21 by decide, Nat.count_add, count_to_800, block_800_821]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_821_900 :
    Nat.count (fun j => Nat.Prime (821 + j)) 79 = 13 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_900 : Nat.count Nat.Prime 900 = 154 := by
  rw [show 900 = 821 + 79 by decide, Nat.count_add, count_to_821, block_821_900]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_900_1000 :
    Nat.count (fun j => Nat.Prime (900 + j)) 100 = 14 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_1000 : Nat.count Nat.Prime 1000 = 168 := by
  rw [show 1000 = 900 + 100 by decide, Nat.count_add, count_to_900, block_900_1000]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_1000_1100 :
    Nat.count (fun j => Nat.Prime (1000 + j)) 100 = 16 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_1100 : Nat.count Nat.Prime 1100 = 184 := by
  rw [show 1100 = 1000 + 100 by decide, Nat.count_add, count_to_1000, block_1000_1100]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_1100_1200 :
    Nat.count (fun j => Nat.Prime (1100 + j)) 100 = 12 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_1200 : Nat.count Nat.Prime 1200 = 196 := by
  rw [show 1200 = 1100 + 100 by decide, Nat.count_add, count_to_1100, block_1100_1200]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_1200_1300 :
    Nat.count (fun j => Nat.Prime (1200 + j)) 100 = 15 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_1300 : Nat.count Nat.Prime 1300 = 211 := by
  rw [show 1300 = 1200 + 100 by decide, Nat.count_add, count_to_1200, block_1200_1300]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_1300_1400 :
    Nat.count (fun j => Nat.Prime (1300 + j)) 100 = 11 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_1400 : Nat.count Nat.Prime 1400 = 222 := by
  rw [show 1400 = 1300 + 100 by decide, Nat.count_add, count_to_1300, block_1300_1400]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_1400_1500 :
    Nat.count (fun j => Nat.Prime (1400 + j)) 100 = 17 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_1500 : Nat.count Nat.Prime 1500 = 239 := by
  rw [show 1500 = 1400 + 100 by decide, Nat.count_add, count_to_1400, block_1400_1500]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_1500_1534 :
    Nat.count (fun j => Nat.Prime (1500 + j)) 34 = 3 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_1534 : Nat.count Nat.Prime 1534 = 242 := by
  rw [show 1534 = 1500 + 34 by decide, Nat.count_add, count_to_1500, block_1500_1534]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_1534_1600 :
    Nat.count (fun j => Nat.Prime (1534 + j)) 66 = 9 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_1600 : Nat.count Nat.Prime 1600 = 251 := by
  rw [show 1600 = 1534 + 66 by decide, Nat.count_add, count_to_1534, block_1534_1600]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_1600_1700 :
    Nat.count (fun j => Nat.Prime (1600 + j)) 100 = 15 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_1700 : Nat.count Nat.Prime 1700 = 266 := by
  rw [show 1700 = 1600 + 100 by decide, Nat.count_add, count_to_1600, block_1600_1700]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_1700_1800 :
    Nat.count (fun j => Nat.Prime (1700 + j)) 100 = 12 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_1800 : Nat.count Nat.Prime 1800 = 278 := by
  rw [show 1800 = 1700 + 100 by decide, Nat.count_add, count_to_1700, block_1700_1800]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_1800_1900 :
    Nat.count (fun j => Nat.Prime (1800 + j)) 100 = 12 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_1900 : Nat.count Nat.Prime 1900 = 290 := by
  rw [show 1900 = 1800 + 100 by decide, Nat.count_add, count_to_1800, block_1800_1900]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_1900_2000 :
    Nat.count (fun j => Nat.Prime (1900 + j)) 100 = 13 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_2000 : Nat.count Nat.Prime 2000 = 303 := by
  rw [show 2000 = 1900 + 100 by decide, Nat.count_add, count_to_1900, block_1900_2000]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_2000_2100 :
    Nat.count (fun j => Nat.Prime (2000 + j)) 100 = 14 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_2100 : Nat.count Nat.Prime 2100 = 317 := by
  rw [show 2100 = 2000 + 100 by decide, Nat.count_add, count_to_2000, block_2000_2100]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_2100_2200 :
    Nat.count (fun j => Nat.Prime (2100 + j)) 100 = 10 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_2200 : Nat.count Nat.Prime 2200 = 327 := by
  rw [show 2200 = 2100 + 100 by decide, Nat.count_add, count_to_2100, block_2100_2200]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_2200_2300 :
    Nat.count (fun j => Nat.Prime (2200 + j)) 100 = 15 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_2300 : Nat.count Nat.Prime 2300 = 342 := by
  rw [show 2300 = 2200 + 100 by decide, Nat.count_add, count_to_2200, block_2200_2300]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_2300_2400 :
    Nat.count (fun j => Nat.Prime (2300 + j)) 100 = 15 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_2400 : Nat.count Nat.Prime 2400 = 357 := by
  rw [show 2400 = 2300 + 100 by decide, Nat.count_add, count_to_2300, block_2300_2400]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_2400_2500 :
    Nat.count (fun j => Nat.Prime (2400 + j)) 100 = 10 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_2500 : Nat.count Nat.Prime 2500 = 367 := by
  rw [show 2500 = 2400 + 100 by decide, Nat.count_add, count_to_2400, block_2400_2500]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_2500_2600 :
    Nat.count (fun j => Nat.Prime (2500 + j)) 100 = 11 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_2600 : Nat.count Nat.Prime 2600 = 378 := by
  rw [show 2600 = 2500 + 100 by decide, Nat.count_add, count_to_2500, block_2500_2600]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma block_2600_2631 :
    Nat.count (fun j => Nat.Prime (2600 + j)) 31 = 3 := by
  rw [Nat.decidablePrime_csimp]
  decide +kernel

private lemma count_to_2631 : Nat.count Nat.Prime 2631 = 381 := by
  rw [show 2631 = 2600 + 31 by decide, Nat.count_add, count_to_2600, block_2600_2631]


private lemma pc_7 : Nat.primeCounting 7 = 4 := count_to_8


private lemma pc_13 : Nat.primeCounting 13 = 6 := count_to_14


private lemma pc_19 : Nat.primeCounting 19 = 8 := count_to_20


private lemma pc_38 : Nat.primeCounting 38 = 12 := count_to_39


private lemma pc_56 : Nat.primeCounting 56 = 16 := count_to_57


private lemma pc_100 : Nat.primeCounting 100 = 25 := count_to_101


private lemma pc_156 : Nat.primeCounting 156 = 36 := count_to_157


private lemma pc_280 : Nat.primeCounting 280 = 59 := count_to_281


private lemma pc_458 : Nat.primeCounting 458 = 88 := count_to_459


private lemma pc_820 : Nat.primeCounting 820 = 141 := count_to_821


private lemma pc_1533 : Nat.primeCounting 1533 = 242 := count_to_1534


private lemma pc_2630 : Nat.primeCounting 2630 = 381 := count_to_2631


lemma checkpoint (l a b u m : ℕ)
    (hcount : a ≤ Nat.primeCounting l) (hpow : 2 ^ b ≤ a) (hb : 0 < b)
    (hnum : 400 * u < 621 * a * b) (hl : l ≤ m) (hu : m ≤ u) :
    (4 / 9 : ℝ) * m < (Nat.primeCounting m : ℝ) * Real.log (Nat.primeCounting m) := by
  have ha : a ≤ Nat.primeCounting m := hcount.trans (Nat.monotone_primeCounting hl)
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity : 0 < 2 ^ b) hpow
  have hA0 : 0 < (Nat.primeCounting m : ℝ) := by exact_mod_cast ha0.trans_le ha
  have hpow' : (2 : ℝ) ^ b ≤ Nat.primeCounting m := by exact_mod_cast hpow.trans ha
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ b) hpow'
  rw [Real.log_pow] at hlog
  have hab : (0 : ℝ) < (a : ℝ) * b := by positivity
  have h69 : (69 / 100 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hstrict := mul_lt_mul_of_pos_left h69 hab
  have han : (a : ℝ) ≤ Nat.primeCounting m := by exact_mod_cast ha
  have h1 := mul_le_mul_of_nonneg_right han
    (show (0 : ℝ) ≤ (b : ℝ) * Real.log 2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hlog (le_of_lt hA0)
  have hnum' : (400 : ℝ) * u < 621 * a * b := by exact_mod_cast hnum
  have hu' : (m : ℝ) ≤ u := by exact_mod_cast hu
  nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma small_log_bound (m : ℕ) (hm : 7 ≤ m) (hm' : m < 4096) :
    (4 / 9 : ℝ) * m < (Nat.primeCounting m : ℝ) * Real.log (Nat.primeCounting m) := by
  by_cases h1 : m ≤ 12
  · exact checkpoint 7 4 2 12 m (by rw [pc_7]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hm h1
  by_cases h2 : m ≤ 18
  · exact checkpoint 13 6 2 18 m (by rw [pc_13]) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega) h2
  by_cases h3 : m ≤ 37
  · exact checkpoint 19 8 3 37 m (by rw [pc_19]) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega) h3
  by_cases h4 : m ≤ 55
  · exact checkpoint 38 12 3 55 m (by rw [pc_38]) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega) h4
  by_cases h5 : m ≤ 99
  · exact checkpoint 56 16 4 99 m (by rw [pc_56]) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega) h5
  by_cases h6 : m ≤ 155
  · exact checkpoint 100 25 4 155 m (by rw [pc_100]) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega) h6
  by_cases h7 : m ≤ 279
  · exact checkpoint 156 36 5 279 m (by rw [pc_156]) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega) h7
  by_cases h8 : m ≤ 457
  · exact checkpoint 280 59 5 457 m (by rw [pc_280]) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega) h8
  by_cases h9 : m ≤ 819
  · exact checkpoint 458 88 6 819 m (by rw [pc_458]) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega) h9
  by_cases h10 : m ≤ 1532
  · exact checkpoint 820 141 7 1532 m (by rw [pc_820]) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega) h10
  by_cases h11 : m ≤ 2629
  · exact checkpoint 1533 242 7 2629 m (by rw [pc_1533]) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega) h11
  exact checkpoint 2630 381 8 4732 m (by rw [pc_2630]) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega) (by omega)

theorem counting_log_bound (m : ℕ) (hm : 7 ≤ m) :
    (4 / 9 : ℝ) * m < (Nat.primeCounting m : ℝ) * Real.log (Nat.primeCounting m) := by
  by_cases h : 4096 ≤ m
  · exact large_log_bound m h
  · exact small_log_bound m hm (by omega)

lemma analytic_step (k A B c : ℝ) (hk : 0 ≤ k) (hA : 0 < A) (hB : 0 < B)
    (hcount : c < A * Real.log A) (hgrowth : k * (B - A) ≤ c) :
    k * Real.log B < (k + 1) * Real.log A := by
  have hratio := Real.log_le_sub_one_of_pos (div_pos hB hA)
  rw [Real.log_div (ne_of_gt hB) (ne_of_gt hA)] at hratio
  have hratio' : Real.log B - Real.log A ≤ (B - A) / A := by
    convert hratio using 1; field_simp
  have hmul : A * (Real.log B - Real.log A) ≤ B - A := by
    simpa [mul_comm] using (le_div_iff₀ hA).1 hratio'
  have hkmul := mul_le_mul_of_nonneg_left hmul hk
  have hfinal : A * (k * (Real.log B - Real.log A)) < A * Real.log A := by nlinarith
  have hcancel : k * (Real.log B - Real.log A) < Real.log A :=
    (mul_lt_mul_iff_right₀ hA).1 hfinal
  linarith

lemma pc_pos (m : ℕ) (hm : 2 ≤ m) : 0 < Nat.primeCounting m := by
  have h : Nat.primeCounting m ≠ 0 := by
    intro hz
    have := Nat.primeCounting_eq_zero_iff.1 hz
    omega
  omega

lemma small_cases (n k : ℕ) (hn : 5 ≤ n) (hk : 1 ≤ k) (hsmall : n * k < 17) :
    Nat.primeCounting ((k + 1) * n) ^ k < Nat.primeCounting (k * n) ^ (k + 1) := by
  have hn' : n ≤ 16 := by nlinarith
  have hk' : k ≤ 3 := by nlinarith
  interval_cases n <;> interval_cases k <;> first | omega | decide

/-- Unconditional integer-power version: no prime-density hypothesis. -/
theorem sun_power (n k : ℕ) (hn : 5 ≤ n) (hk : 1 ≤ k) :
    Nat.primeCounting ((k + 1) * n) ^ k < Nat.primeCounting (k * n) ^ (k + 1) := by
  by_cases hx : 17 ≤ k * n
  · have hx7 : 7 ≤ k * n := by omega
    have hnext2 : 2 ≤ (k + 1) * n := by nlinarith
    have hA : 0 < (Nat.primeCounting (k * n) : ℝ) := by
      exact_mod_cast pc_pos (k * n) (by omega)
    have hB : 0 < (Nat.primeCounting ((k + 1) * n) : ℝ) := by
      exact_mod_cast pc_pos ((k + 1) * n) hnext2
    have hdiff := pc_interval_four_ninths (k * n) n hx7 hn
    have hmono := Nat.monotone_primeCounting (show k * n ≤ k * n + n by omega)
    have hcast : (9 : ℝ) * ((Nat.primeCounting (k * n + n) : ℝ) -
        (Nat.primeCounting (k * n) : ℝ)) ≤ 4 * (n : ℝ) := by
      exact_mod_cast hdiff
    have heq : (k + 1) * n = k * n + n := by ring
    have hgrowth : (k : ℝ) * ((Nat.primeCounting ((k + 1) * n) : ℝ) -
        (Nat.primeCounting (k * n) : ℝ)) ≤ (4 / 9 : ℝ) * (k * n : ℕ) := by
      rw [heq]
      push_cast
      have hknonneg : (0 : ℝ) ≤ k := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hcast hknonneg]
    have hlog := analytic_step k
      (Nat.primeCounting (k * n)) (Nat.primeCounting ((k + 1) * n))
      ((4 / 9 : ℝ) * (k * n : ℕ)) (by positivity) hA hB
      (counting_log_bound (k * n) hx7) hgrowth
    have hpow : (Nat.primeCounting ((k + 1) * n) : ℝ) ^ k <
        (Nat.primeCounting (k * n) : ℝ) ^ (k + 1) := by
      apply (Real.log_lt_log_iff (pow_pos hB _) (pow_pos hA _)).1
      simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using hlog
    exact_mod_cast hpow
  · exact small_cases n k hn hk (by nlinarith)

/-- Sun's Conjecture 2.7(i), with the restriction k <= n removed. -/
theorem sun_roots (n k : ℕ) (hn : 5 ≤ n) (hk : 1 ≤ k) :
    (Nat.primeCounting ((k + 1) * n) : ℝ) ^ (1 / ((k : ℝ) + 1)) <
      (Nat.primeCounting (k * n) : ℝ) ^ (1 / (k : ℝ)) := by
  have hA : 0 < (Nat.primeCounting (k * n) : ℝ) := by
    exact_mod_cast pc_pos (k * n) (by nlinarith)
  have hB : 0 < (Nat.primeCounting ((k + 1) * n) : ℝ) := by
    exact_mod_cast pc_pos ((k + 1) * n) (by nlinarith)
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpow : (Nat.primeCounting ((k + 1) * n) : ℝ) ^ k <
      (Nat.primeCounting (k * n) : ℝ) ^ (k + 1) := by
    exact_mod_cast sun_power n k hn hk
  have hlog := Real.log_lt_log (pow_pos hB k) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hB _) (Real.rpow_pos_of_pos hA _)).1
  rw [Real.log_rpow hB, Real.log_rpow hA]
  simp only [one_div_mul_eq_div]
  apply (div_lt_div_iff₀ (by linarith : (0 : ℝ) < (k : ℝ) + 1) hkr).2
  nlinarith

#print axioms sun_power
#print axioms sun_roots
#check sun_roots

end SunComplete
