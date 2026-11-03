import Sunproj.Triple.Gap
import Sunproj.Triple.Count
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Nth

/-!
# A counterexample to Sun's Conjecture 2.9 (arXiv:1208.2683): `E(x, x + 4, x + 6) ≠ ∅`

Let `q_1 < q_2 < …` be the positive integers `x` with `x`, `x + 4`, `x + 6` all prime. Sun
conjectures that `q_(n+1) < q_n ^ (1 + 1/n)` for every `n ≥ 1`. It fails for `n = 77055`:
`q_n = 148770907`, `q_(n+1) = 148809247`.

The proof needs only a lower bound `n ≥ 77055`: the inequality fails for every `n ≥ 73029`.
-/

namespace Triple

/-- `q_n` in Sun's notation, 1-indexed. -/
noncomputable def q (n : ℕ) : ℕ := Nat.nth IsT (n - 1)

/-- Sun's Conjecture 2.9, the part `E(x, x + 4, x + 6) = ∅`. -/
def SunConj29 : Prop := ∀ n : ℕ, 1 ≤ n → (q (n + 1) : ℝ) < (q n : ℝ) ^ (1 + 1 / (n : ℝ))

lemma qn_mem : IsT 148770907 := mem_of_count (run_sound0 qn_ok)

lemma qn1_mem : IsT 148809247 := mem_of_count (run_sound0 qn1_ok)

lemma pow_step {A B L n : ℕ} (hB : 0 < B) (hAB : A ≤ B) (h : A ^ (L + 1) < B ^ L) (hn : L ≤ n) :
    A ^ (n + 1) < B ^ n := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show L + t + 1 = (L + 1) + t by omega, pow_add A (L + 1) t, pow_add B L t]
  exact Nat.mul_lt_mul_of_lt_of_le h (Nat.pow_le_pow_left hAB t) (pow_pos hB t)

lemma big_pow : (148770907 : ℕ) ^ (77055 + 1) < 148809247 ^ 77055 := by decide +kernel

/-- The violation: `q_n ^ (1 + 1/n) < q_(n+1)` for some `n ≥ 77055`. -/
theorem sun29_counterexample : ∃ n : ℕ, 77055 ≤ n ∧ q n = 148770907 ∧
    q (n + 1) = 148809247 ∧ (148770907 : ℝ) ^ (1 + 1 / (n : ℝ)) < 148809247 := by
  obtain ⟨c, hc⟩ : ∃ c, Nat.count IsT 148770907 = c := ⟨_, rfl⟩
  have hc1 : Nat.count IsT 148770908 = c + 1 := by
    rw [show (148770908 : ℕ) = 148770907 + 1 from rfl, Nat.count_succ, hc]
    simp only [qn_mem, ite_true]
  have hlow := count_le
  have hN2 : Nat.count IsT 148809247 = c + 1 := gap_count.trans hc1
  refine ⟨c + 1, by omega, ?_, ?_, ?_⟩
  · simp only [q, Nat.add_sub_cancel]
    rw [← hc]
    exact Nat.nth_count qn_mem
  · simp only [q, Nat.add_sub_cancel]
    rw [← hN2]
    exact Nat.nth_count qn1_mem
  · have hnat : (148770907 : ℕ) ^ (c + 1 + 1) < 148809247 ^ (c + 1) :=
      pow_step (by norm_num) (by norm_num) big_pow (by omega)
    have hreal : (((148770907 : ℝ) ^ (1 + 1 / ((c + 1 : ℕ) : ℝ))) ^ (c + 1)) <
        (148809247 : ℝ) ^ (c + 1) := by
      rw [← Real.rpow_mul_natCast (by norm_num)]
      have : (1 + 1 / ((c + 1 : ℕ) : ℝ)) * ((c + 1 : ℕ) : ℝ) = ((c + 1 + 1 : ℕ) : ℝ) := by
        push_cast; field_simp
      rw [this, Real.rpow_natCast]
      exact_mod_cast hnat
    exact lt_of_pow_lt_pow_left₀ (c + 1) (by norm_num) hreal

/-- **Sun's Conjecture 2.9 is false**: `E(x, x + 4, x + 6) ≠ ∅`. -/
theorem sun29_false : ¬ SunConj29 := by
  intro h
  obtain ⟨n, hn, h1, h2, h3⟩ := sun29_counterexample
  have := h n (by omega)
  rw [h1, h2] at this
  push_cast at this
  linarith

end Triple
