import Sunproj.PrimRoot.Checker

/-!
# A kernel-checkable certificate format for prime triples `x, x + 4, x + 6`

This file defines the predicate of Sun's Conjecture 2.9 for the family `(x, x + 4, x + 6)` and a
Boolean checker for certificates of it. The Lucas certificates `PrimRoot.certPrime` are reused.

* `run`: a stream of members `x` in increasing order, each followed by Lucas certificates of
  `x`, `x + 4` and `x + 6`.
* `runGap`: every integer of a range is shown not to be a member, by a divisor `d` with
  `2 ≤ d < x` of one of `x`, `x + 4`, `x + 6`.

Soundness: `run_sound` turns an accepted stream into a lower bound for `Nat.count`, and
`runGap_sound` into an equality.
-/

namespace Triple

open PrimRoot

/-- `x`, `x + 4` and `x + 6` are all prime. -/
def IsT (x : ℕ) : Prop := x.Prime ∧ (x + 4).Prime ∧ (x + 6).Prime

noncomputable instance : DecidablePred IsT := Classical.decPred _

/-! ### The checker -/

/-- Reads members `x = nxt + d` in increasing order, each with three Lucas certificates; returns
the next free value and the updated number of members. -/
def run : ℕ → ℕ → ℕ → List ℕ → Option (ℕ × ℕ)
  | _, nxt, cnt, [] => some (nxt, cnt)
  | f + 1, nxt, cnt, d :: l =>
      match certPrime 32 (nxt + d) l with
      | some l₁ =>
        match certPrime 32 (nxt + d + 4) l₁ with
        | some l₂ =>
          match certPrime 32 (nxt + d + 6) l₂ with
          | some l₃ => run f (nxt + d + 1) (cnt + 1) l₃
          | none => none
        | none => none
      | none => none
  | _, _, _, _ => none

/-- Shows that `nxt, nxt + 1, …` are not members: each token `d` with `2 ≤ d < nxt` divides one
of `nxt`, `nxt + 4`, `nxt + 6`. -/
def runGap : ℕ → ℕ → List ℕ → Option ℕ
  | _, nxt, [] => some nxt
  | f + 1, nxt, d :: l =>
      if 2 ≤ d && d < nxt && (nxt % d == 0 || (nxt + 4) % d == 0 || (nxt + 6) % d == 0) then
        runGap f (nxt + 1) l
      else none
  | _, _, _ => none

/-! ### Soundness -/

lemma not_prime_of_mod {m d : ℕ} (h2 : 2 ≤ d) (hlt : d < m) (hd : m % d = 0) : ¬ m.Prime := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hd) with h | h <;> omega

/-- An accepted member stream gives a lower bound for the counting function. -/
lemma run_sound : ∀ f nxt cnt l nxt' cnt', run f nxt cnt l = some (nxt', cnt') →
    Nat.count IsT nxt + cnt' ≤ Nat.count IsT nxt' + cnt := by
  intro f
  induction f with
  | zero =>
    intro nxt cnt l nxt' cnt' h
    match l, h with
    | [], h =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact le_refl _
    | _ :: _, h => simp [run] at h
  | succ f ih =>
    intro nxt cnt l nxt' cnt' h
    match l, h with
    | [], h =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact le_refl _
    | d :: l, h =>
      simp only [run] at h
      split at h
      · rename_i l₁ h₁
        split at h
        · rename_i l₂ h₂
          split at h
          · rename_i l₃ h₃
            have hmem : IsT (nxt + d) :=
              ⟨certPrime_sound _ _ _ _ h₁, certPrime_sound _ _ _ _ h₂,
                certPrime_sound _ _ _ _ h₃⟩
            have := ih _ _ _ _ _ h
            have hmono := Nat.count_monotone IsT (Nat.le_add_right nxt d)
            simp only [Nat.count_succ, hmem, ite_true] at this
            omega
          · simp at h
        · simp at h
      · simp at h

/-- `run_sound` for a stream started with count 0. -/
lemma run_sound0 {f nxt nxt' c : ℕ} {l : List ℕ} (h : run f nxt 0 l = some (nxt', c)) :
    Nat.count IsT nxt + c ≤ Nat.count IsT nxt' :=
  run_sound f nxt 0 l nxt' c h

/-- An accepted gap stream shows that the range contains no member. -/
lemma runGap_sound : ∀ f nxt l nxt', runGap f nxt l = some nxt' →
    Nat.count IsT nxt' = Nat.count IsT nxt := by
  intro f
  induction f with
  | zero =>
    intro nxt l nxt' h
    match l, h with
    | [], h => simp only [runGap, Option.some.injEq] at h; rw [h]
    | _ :: _, h => simp [runGap] at h
  | succ f ih =>
    intro nxt l nxt' h
    match l, h with
    | [], h => simp only [runGap, Option.some.injEq] at h; rw [h]
    | d :: l, h =>
      simp only [runGap] at h
      split_ifs at h with h1
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
      obtain ⟨⟨h2, hlt⟩, hd⟩ := h1
      have hn : ¬ IsT nxt := by
        rintro ⟨p0, p4, p6⟩
        rcases hd with (hd | hd) | hd
        · exact not_prime_of_mod h2 hlt hd p0
        · exact not_prime_of_mod h2 (by omega) hd p4
        · exact not_prime_of_mod h2 (by omega) hd p6
      rw [ih _ _ _ h]
      simp [Nat.count_succ, hn]

/-- A one-element stream certifies a member. -/
lemma mem_of_count {x : ℕ} (h : Nat.count IsT x + 1 ≤ Nat.count IsT (x + 1)) : IsT x := by
  rw [Nat.count_succ] at h
  split_ifs at h with hx
  · exact hx
  · omega

end Triple
