# Writes the Lean data files for the counterexample to Sun 2.4(ii):
#   Sunproj/PrimRoot/Data/Cnnn.lean  members 1 .. 754589 (the last one is p_n = 51459203)
#   Sunproj/PrimRoot/Gap.lean        p_n and p_{n+1} = 51460433 are members, nothing in between
import pickle, sys, os
sys.path.insert(0, os.path.dirname(__file__))
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../Sunproj/PrimRoot')
N1, N2, NIDX = 51459203, 51460433, 754589
CH = 2000
toks = pickle.load(open(os.path.join(os.path.dirname(__file__), 'members.pkl'), 'rb'))
assert toks[NIDX - 1][0] == N1 and toks[NIDX][0] == N2
def lit(flat):
    return ',\n  '.join(', '.join(map(str, flat[i:i + 16])) for i in range(0, len(flat), 16))
HDR = 'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n'
os.makedirs(OUT + '/Data', exist_ok=True)
names = []
for c, a in enumerate(range(0, NIDX, CH)):
    b = min(a + CH, NIDX)
    nxt = 0 if a == 0 else toks[a - 1][0] + 1
    hi = toks[b - 1][0] + 1
    flat = [x for _, t in toks[a:b] for x in t]
    nm = 'C%03d' % c; names.append((nm, nxt, hi, b - a))
    open(f'{OUT}/Data/{nm}.lean', 'w').write(f'''import Sunproj.PrimRoot.Checker

/-! Certificates for the members {a + 1}–{b} of Sun's sequence for `a = -3` (generated). -/

namespace PrimRoot

{HDR}/-- Certificate tokens. -/
def D{nm} : List ℕ := [
  {lit(flat)}]

{HDR}lemma D{nm}_ok : run {b - a} {nxt} 0 D{nm} = some ({hi}, {b - a}) := by decide +kernel

lemma D{nm}_count :
    Nat.count (IsLNPR (-3)) {nxt} + {b - a} ≤ Nat.count (IsLNPR (-3)) {hi} :=
  run_sound0 D{nm}_ok

end PrimRoot
''')
pickle.dump(names, open(os.path.join(os.path.dirname(__file__), 'chunks.pkl'), 'wb'))
print(len(names), 'chunks')
# gap certificate
import numpy as np
from gen_data import factors, split, cert, is_pr
gap = []
for k in range(N1 + 1, N2):
    f = factors(k)
    if f[0] != k: gap += [0, f[0]]; continue
    fs = factors(k - 1)
    w = next((r for r in fs if pow(k - 3, (k - 1) // r, k) == 1), None)
    if w is not None: gap += [1, w]; continue
    assert is_pr(k - 2, k, fs), k
    _, ss, R = split(k - 1)
    gap += [2, len(ss)] + ss + (cert(R) if R > 1 else [])
t1 = toks[NIDX - 1][1][:]; t1[0] = 0
t2 = toks[NIDX][1][:]; t2[0] = 0
open(f'{OUT}/Gap.lean', 'w').write(f'''import Sunproj.PrimRoot.Checker

/-! `p_n = {N1}` and `p_(n+1) = {N2}` are members, and nothing in between is (generated). -/

namespace PrimRoot

{HDR}/-- Non-membership certificates for `{N1 + 1} … {N2 - 1}`. -/
def gapData : List ℕ := [
  {lit(gap)}]

{HDR}lemma gap_ok : runGap {N2 - N1 - 1} {N1 + 1} gapData = some {N2} := by decide +kernel

lemma gap_count : Nat.count (IsLNPR (-3)) {N2} = Nat.count (IsLNPR (-3)) {N1 + 1} :=
  runGap_sound _ _ _ _ gap_ok

lemma pn_ok : run 1 {N1} 0 {t1} = some ({N1 + 1}, 1) := by decide +kernel

lemma pn1_ok : run 1 {N2} 0 {t2} = some ({N2 + 1}, 1) := by decide +kernel

end PrimRoot
''')
print('gap tokens', len(gap))

# final theorem file
imports = '\n'.join(f'import Sunproj.PrimRoot.Data.{nm}' for nm, _, _, _ in names)
chain = []
acc = 0; prev = '(Nat.zero_le _)'
for i, (nm, lo, hi, c) in enumerate(names):
    acc += c
    chain.append(f'  have h{i} : {acc} ≤ Nat.count (IsLNPR (-3)) {hi} := chain {prev} D{nm}_count rfl')
    prev = f'h{i}'
assert acc == NIDX
chain.append(f'  exact h{len(names) - 1}')
open(f'{OUT}/Sun24.lean', 'w').write(f'''import Sunproj.PrimRoot.Gap
{imports}
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Nth

/-!
# Sun's Conjecture 2.4(ii) (arXiv:1208.2683) is false

Let `p_n(a)` be the `n`-th prime for which `a < 0` is the largest negative primitive root.
Sun conjectured that `p_(n+1)(a) < p_n(a) ^ (1 + 1/n)` for every `a < 0` that is not a perfect
power and every `n ≥ 1`, with the single exception `a = -2`, `n = 13`.

For `a = -3` the primes `p_n = {N1}` and `p_(n+1) = {N2}` are consecutive members, and
`n ≥ {NIDX}` (in fact `n = {NIDX}`). This already violates the inequality, since
`{N1} ^ ({NIDX} + 1) > {N2} ^ {NIDX}`.

The lower bound for `n` is a kernel check of {NIDX} member certificates (`Data/C*.lean`); the
two members and the empty gap between them are checked in `Gap.lean`.
-/

namespace PrimRoot

/-- `p_n(a)` in Sun's notation, 1-indexed. -/
noncomputable def sunP (a : ℤ) (n : ℕ) : ℕ := Nat.nth (IsLNPR a) (n - 1)

/-- `a` is a perfect power: `a = x ^ m` for some integers `x` and `m > 1`. -/
def IsPerfectPower (a : ℤ) : Prop := ∃ m : ℕ, 1 < m ∧ ∃ x : ℤ, x ^ m = a

/-- Sun's Conjecture 2.4(ii), the inequality part. -/
def SunConj24ii : Prop :=
  ∀ a : ℤ, a < 0 → ¬ IsPerfectPower a → ∀ n : ℕ, 1 ≤ n → ¬ (a = -2 ∧ n = 13) →
    (sunP a (n + 1) : ℝ) < (sunP a n : ℝ) ^ (1 + 1 / (n : ℝ))

lemma chain {{a b lo hi c : ℕ}} (ha : a ≤ Nat.count (IsLNPR (-3)) lo)
    (h : Nat.count (IsLNPR (-3)) lo + c ≤ Nat.count (IsLNPR (-3)) hi) (hb : b = a + c) :
    b ≤ Nat.count (IsLNPR (-3)) hi := by omega

/-- At least {NIDX} members are `≤ {N1}`. -/
theorem count_le : {NIDX} ≤ Nat.count (IsLNPR (-3)) {N1 + 1} := by
{chr(10).join(chain)}

lemma mem_of_count {{x : ℕ}}
    (h : Nat.count (IsLNPR (-3)) x + 1 ≤ Nat.count (IsLNPR (-3)) (x + 1)) : IsLNPR (-3) x := by
  rw [Nat.count_succ] at h
  split_ifs at h with hx
  · exact hx
  · omega

lemma pn_mem : IsLNPR (-3) {N1} := mem_of_count (run_sound0 pn_ok)

lemma pn1_mem : IsLNPR (-3) {N2} := mem_of_count (run_sound0 pn1_ok)

lemma pow_step {{A B L n : ℕ}} (hB : 0 < B) (hAB : A ≤ B) (h : A ^ (L + 1) < B ^ L) (hn : L ≤ n) :
    A ^ (n + 1) < B ^ n := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show L + t + 1 = (L + 1) + t by omega, pow_add A (L + 1) t, pow_add B L t]
  exact Nat.mul_lt_mul_of_lt_of_le h (Nat.pow_le_pow_left hAB t) (pow_pos hB t)

lemma big_pow : ({N1} : ℕ) ^ ({NIDX} + 1) < {N2} ^ {NIDX} := by decide +kernel

/-- The violation: `p_n ^ (1 + 1/n) < p_(n+1)` for `a = -3` and some `n ≥ {NIDX}`. -/
theorem sun24ii_counterexample : ∃ n : ℕ, {NIDX} ≤ n ∧ sunP (-3) n = {N1} ∧
    sunP (-3) (n + 1) = {N2} ∧ ({N1} : ℝ) ^ (1 + 1 / (n : ℝ)) < {N2} := by
  obtain ⟨c, hc⟩ : ∃ c, Nat.count (IsLNPR (-3)) {N1} = c := ⟨_, rfl⟩
  have hc1 : Nat.count (IsLNPR (-3)) {N1 + 1} = c + 1 := by
    rw [show ({N1 + 1} : ℕ) = {N1} + 1 from rfl, Nat.count_succ, hc]
    simp only [pn_mem, ite_true]
  have hlow := count_le
  have hN2 : Nat.count (IsLNPR (-3)) {N2} = c + 1 := gap_count.trans hc1
  refine ⟨c + 1, by omega, ?_, ?_, ?_⟩
  · simp only [sunP, Nat.add_sub_cancel]
    rw [← hc]
    exact Nat.nth_count pn_mem
  · simp only [sunP, Nat.add_sub_cancel]
    rw [← hN2]
    exact Nat.nth_count pn1_mem
  · have hn : 0 < c + 1 := by omega
    have hnat : ({N1} : ℕ) ^ (c + 1 + 1) < {N2} ^ (c + 1) :=
      pow_step (by norm_num) (by norm_num) big_pow (by omega)
    have hreal : ((({N1} : ℝ) ^ (1 + 1 / ((c + 1 : ℕ) : ℝ))) ^ (c + 1)) < ({N2} : ℝ) ^ (c + 1) := by
      rw [← Real.rpow_mul_natCast (by norm_num)]
      have : (1 + 1 / ((c + 1 : ℕ) : ℝ)) * ((c + 1 : ℕ) : ℝ) = ((c + 1 + 1 : ℕ) : ℝ) := by
        push_cast; field_simp
      rw [this, Real.rpow_natCast]
      exact_mod_cast hnat
    exact lt_of_pow_lt_pow_left₀ (c + 1) (by norm_num) hreal

lemma not_perfect_power_neg_three : ¬ IsPerfectPower (-3) := by
  rintro ⟨m, hm, x, hx⟩
  have h3 : x.natAbs ^ m = 3 := by rw [← Int.natAbs_pow, hx]; rfl
  rcases Nat.lt_or_ge x.natAbs 2 with h | h
  · interval_cases (x.natAbs)
    · rw [zero_pow (by omega)] at h3; omega
    · rw [one_pow] at h3; omega
  · have h1 := Nat.pow_le_pow_left h m
    have h2 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega

/-- **Sun's Conjecture 2.4(ii) is false.** -/
theorem sun24ii_false : ¬ SunConj24ii := by
  intro h
  obtain ⟨n, hn, h1, h2, h3⟩ := sun24ii_counterexample
  have := h (-3) (by norm_num) not_perfect_power_neg_three n (by omega) (by omega)
  rw [h1, h2] at this
  push_cast at this
  linarith

end PrimRoot
''')
print('wrote Sun24.lean')
