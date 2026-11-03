import Sunproj.PrimRoot.SmallPrimes
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Count

/-!
# A kernel-checkable certificate format for primitive roots

This file defines the predicate of Sun's Conjecture 2.4(ii) (`a` is the largest negative
primitive root modulo `p`) and a Boolean checker for certificates of it. The data is read as a
flat list of naturals; the checker uses only GMP-accelerated kernel operations.

* `certPrime`: a Lucas certificate. It gives a generator `g` and the odd prime factors of
  `q - 1` below `2¹⁶`; the cofactor `R` left after removing them (and 2) is either 1 or a prime
  with a nested certificate.
* `run`: a stream of members `p` of the sequence for `a = -3`, in increasing order. Each member
  is certified by Lucas's test with generator `-3`, and by a witness that `-2` is not a
  primitive root: either `p % 8 ∈ {1, 3}` (then `-2` is a square), or a divisor `w` of `p - 1`
  with `(-2) ^ ((p - 1) / w) = 1`.
* `runGap`: every integer of a range is shown not to be a member.

Soundness: `run_sound` turns an accepted stream into a lower bound for `Nat.count`, and
`runGap_sound` into an equality.
-/

namespace PrimRoot

/-- `a` is a primitive root modulo `p`. -/
def IsPrimRoot (a : ℤ) (p : ℕ) : Prop := orderOf (a : ZMod p) = p - 1

/-- `a` is the largest negative primitive root modulo the prime `p`: no `b` with `a < b < 0` is
a primitive root. -/
def IsLNPR (a : ℤ) (p : ℕ) : Prop :=
  p.Prime ∧ IsPrimRoot a p ∧ ∀ b : ℤ, a < b → b < 0 → ¬ IsPrimRoot b p

noncomputable instance (a : ℤ) : DecidablePred (IsLNPR a) := Classical.decPred _

/-! ### The checker -/

/-- `b ^ e % q`, computed with base-1024 digits of `e` so that the kernel uses GMP powers. -/
def powMod (q b : ℕ) : ℕ → ℕ → ℕ
  | 0, e => b ^ e % q
  | f + 1, e =>
      if e < 1024 then b ^ e % q else (powMod q b f (e / 1024) ^ 1024 * b ^ (e % 1024)) % q

/-- `b ^ e % q` for `e < 2³⁰`. -/
def pm (q b e : ℕ) : ℕ := powMod q b 3 e

/-- Lucas's conditions for the generator `g` modulo `q`: `g ^ ((q-1)/2) = -1`, and
`g ^ ((q-1)/r) ≠ 1` for every listed odd prime factor `r` and for the cofactor `R`. -/
def lucasOK (q g : ℕ) (ss : List ℕ) (R : ℕ) : Bool :=
  3 ≤ q && (q - 1) % 2 == 0 && pm q g ((q - 1) / 2) == q - 1 &&
    ss.all (fun s => pm q g ((q - 1) / s) != 1) && (R == 1 || pm q g ((q - 1) / R) != 1)

/-- What is left of `m` after removing every prime dividing `2 * ss.prod`. -/
def cofactor (m : ℕ) (ss : List ℕ) : ℕ := m / Nat.gcd m ((2 * ss.prod) ^ 32)

/-- Reads a Lucas certificate for `q` from the front of the list (generator, number of small
odd factors, the factors, then the certificate of the cofactor) and returns the rest. -/
def certPrime : ℕ → ℕ → List ℕ → Option (List ℕ)
  | f + 1, q, g :: k :: l =>
      if (l.take k).all smallPrime && lucasOK q g (l.take k) (cofactor (q - 1) (l.take k)) then
        if cofactor (q - 1) (l.take k) == 1 then some (l.drop k)
        else certPrime f (cofactor (q - 1) (l.take k)) (l.drop k)
      else none
  | _, _, _ => none

/-- `-2` is not a primitive root modulo `p`: `w = 0` stands for `p % 8 ∈ {1, 3}`, otherwise
`(-2) ^ ((p - 1) / w) = 1`. -/
def negTwoOK (p w : ℕ) : Bool :=
  if w = 0 then p % 8 == 1 || p % 8 == 3
  else 2 ≤ w && (p - 1) % w == 0 && pm p (p - 2) ((p - 1) / w) == 1

/-- The arithmetic conditions for a member `p` with small factors `ss` and cofactor `R`. -/
def memberOK (p w : ℕ) (ss : List ℕ) (R : ℕ) : Bool :=
  5 ≤ p && ss.all smallPrime && lucasOK p (p - 3) ss R && negTwoOK p w

/-- The certificate of the cofactor `R` (nothing if `R = 1`). -/
def certCof (R : ℕ) (l : List ℕ) : Option (List ℕ) :=
  if R == 1 then some l else certPrime 32 R l

/-- Reads members `p = nxt + d` in increasing order; returns the next free value and the
updated number of members. -/
def run : ℕ → ℕ → ℕ → List ℕ → Option (ℕ × ℕ)
  | _, nxt, cnt, [] => some (nxt, cnt)
  | f + 1, nxt, cnt, d :: w :: k :: l =>
      if memberOK (nxt + d) w (l.take k) (cofactor (nxt + d - 1) (l.take k)) then
        match certCof (cofactor (nxt + d - 1) (l.take k)) (l.drop k) with
        | some l' => run f (nxt + d + 1) (cnt + 1) l'
        | none => none
      else none
  | _, _, _, _ => none

/-- Shows that `nxt, nxt + 1, …` are not members: tag 0 with a proper divisor, tag 1 with a
witness that `-3` is not a primitive root, tag 2 with a certificate that `-2` is one. -/
def runGap : ℕ → ℕ → List ℕ → Option ℕ
  | _, nxt, [] => some nxt
  | f + 1, nxt, 0 :: d :: l =>
      if 2 ≤ d && d < nxt && nxt % d == 0 then runGap f (nxt + 1) l else none
  | f + 1, nxt, 1 :: w :: l =>
      if 5 ≤ nxt && 2 ≤ w && (nxt - 1) % w == 0 && pm nxt (nxt - 3) ((nxt - 1) / w) == 1
      then runGap f (nxt + 1) l else none
  | f + 1, nxt, 2 :: k :: l =>
      if (l.take k).all smallPrime &&
          lucasOK nxt (nxt - 2) (l.take k) (cofactor (nxt - 1) (l.take k)) then
        match certCof (cofactor (nxt - 1) (l.take k)) (l.drop k) with
        | some l' => runGap f (nxt + 1) l'
        | none => none
      else none
  | _, _, _ => none

/-! ### Arithmetic lemmas -/

lemma powMod_eq (q b : ℕ) : ∀ f e, powMod q b f e = b ^ e % q := by
  intro f
  induction f with
  | zero => intro e; rfl
  | succ f ih =>
    intro e
    simp only [powMod]
    split_ifs
    · rfl
    · have he : b ^ e = (b ^ (e / 1024)) ^ 1024 * b ^ (e % 1024) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod']
      rw [ih, he, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod]

lemma pm_eq (q b e : ℕ) : pm q b e = b ^ e % q := powMod_eq q b 3 e

/-- A computed power, read in `ZMod q`. -/
lemma zmod_pow_eq (q b e : ℕ) : ((b : ZMod q)) ^ e = ((pm q b e : ℕ) : ZMod q) := by
  rw [pm_eq, ZMod.natCast_mod, Nat.cast_pow]

lemma zmod_eq_one_iff {q x : ℕ} (hq : 2 ≤ q) (hx : x < q) : ((x : ℕ) : ZMod q) = 1 ↔ x = 1 := by
  rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt (by omega)]

lemma pm_lt {q : ℕ} (hq : 0 < q) (b e : ℕ) : pm q b e < q := by
  rw [pm_eq]; exact Nat.mod_lt _ hq

lemma cast_sub_nat {q c : ℕ} (hc : c ≤ q) : (((q - c : ℕ) : ℕ) : ZMod q) = -(c : ZMod q) := by
  rw [Nat.cast_sub hc, ZMod.natCast_self, zero_sub]

lemma cast_neg_int {q c : ℕ} (hc : c ≤ q) : (((-(c : ℤ)) : ℤ) : ZMod q) = ((q - c : ℕ) : ZMod q) := by
  rw [cast_sub_nat hc]; push_cast; ring

/-- Every prime factor of `m` divides `2 * ss.prod` or the cofactor. -/
lemma dvd_cofactor_of_not_dvd {m r : ℕ} {ss : List ℕ} (hr : r.Prime) (hm : r ∣ m)
    (hn : ¬ r ∣ 2 * ss.prod) : r ∣ cofactor m ss := by
  unfold cofactor
  have hG : Nat.gcd m ((2 * ss.prod) ^ 32) ∣ m := Nat.gcd_dvd_left _ _
  have hcop : Nat.Coprime r (Nat.gcd m ((2 * ss.prod) ^ 32)) := by
    apply Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hr).2 hn)
  have hmul : m = Nat.gcd m ((2 * ss.prod) ^ 32) * (m / Nat.gcd m ((2 * ss.prod) ^ 32)) :=
    (Nat.mul_div_cancel' hG).symm
  rw [hmul] at hm
  exact hcop.dvd_of_dvd_mul_left hm

/-- A prime dividing `2 * ss.prod` with all `ss` prime is 2 or lies in `ss`. -/
lemma mem_of_dvd_prod {r : ℕ} {ss : List ℕ} (hr : r.Prime) (hss : ∀ s ∈ ss, s.Prime)
    (h : r ∣ 2 * ss.prod) : r = 2 ∨ r ∈ ss := by
  rcases (Nat.Prime.dvd_mul hr).1 h with h2 | hp
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
  · obtain ⟨s, hs, hrs⟩ := (Prime.dvd_prod_iff hr.prime).1 hp
    exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr (hss s hs)).1 hrs ▸ hs)

/-! ### Soundness of Lucas certificates -/

lemma lucasOK_three {q g R : ℕ} {ss : List ℕ} (h : lucasOK q g ss R = true) : 3 ≤ q := by
  simp only [lucasOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

/-- Lucas's test as checked by `lucasOK`. -/
lemma lucas_sound {q g : ℕ} {ss : List ℕ} (hss : ∀ s ∈ ss, s.Prime)
    (hR : cofactor (q - 1) ss = 1 ∨ (cofactor (q - 1) ss).Prime)
    (h : lucasOK q g ss (cofactor (q - 1) ss) = true) :
    q.Prime ∧ orderOf (g : ZMod q) = q - 1 := by
  simp only [lucasOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    bne_iff_ne, ne_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨h3, heven⟩, hhalf⟩, hsmall⟩, hcof⟩ := h
  have hq0 : 0 < q := by omega
  have h2q : 2 < q := by omega
  have : Fact (2 < q) := ⟨h2q⟩
  -- `g ^ ((q-1)/2) = -1`
  have hneg : (g : ZMod q) ^ ((q - 1) / 2) = -1 := by
    rw [zmod_pow_eq, hhalf, cast_sub_nat (by omega), Nat.cast_one]
  have hfull : (g : ZMod q) ^ (q - 1) = 1 := by
    have : q - 1 = (q - 1) / 2 * 2 := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero heven)).symm
    rw [this, pow_mul, hneg]; norm_num
  have hne1 : ∀ e, pm q g e ≠ 1 → (g : ZMod q) ^ e ≠ 1 := by
    intro e he hcon
    rw [zmod_pow_eq, zmod_eq_one_iff (by omega) (pm_lt hq0 _ _)] at hcon
    exact he hcon
  have hd : ∀ r : ℕ, r.Prime → r ∣ q - 1 → (g : ZMod q) ^ ((q - 1) / r) ≠ 1 := by
    intro r hr hrd
    by_cases hdiv : r ∣ 2 * ss.prod
    · rcases mem_of_dvd_prod hr hss hdiv with rfl | hmem
      · rw [hneg]; exact ZMod.neg_one_ne_one
      · exact hne1 _ (hsmall r hmem)
    · have hrc := dvd_cofactor_of_not_dvd hr hrd hdiv
      rcases hR with h1 | hRp
      · rw [h1] at hrc; exact absurd (Nat.le_of_dvd one_pos hrc) (by have := hr.two_le; omega)
      · have hrR : r = cofactor (q - 1) ss := (Nat.prime_dvd_prime_iff_eq hr hRp).1 hrc
        rcases hcof with h1 | h1
        · rw [h1] at hRp; exact absurd hRp Nat.not_prime_one
        · rw [hrR]; exact hne1 _ h1
  exact ⟨lucas_primality q _ hfull hd,
    orderOf_eq_of_pow_and_pow_div_prime (by omega) hfull hd⟩

lemma certPrime_sound : ∀ f q l l', certPrime f q l = some l' → q.Prime := by
  intro f
  induction f with
  | zero => intro q l l' h; simp [certPrime] at h
  | succ f ih =>
    intro q l l' h
    match l, h with
    | g :: k :: l, h =>
      simp only [certPrime] at h
      split_ifs at h with h1 h2
      · simp only [Bool.and_eq_true, List.all_eq_true] at h1
        exact (lucas_sound (fun s hs => smallPrime_prime (h1.1 s hs)) (Or.inl (by simpa using h2))
          h1.2).1
      · simp only [Bool.and_eq_true, List.all_eq_true] at h1
        exact (lucas_sound (fun s hs => smallPrime_prime (h1.1 s hs)) (Or.inr (ih _ _ _ h))
          h1.2).1
    | [], h => simp [certPrime] at h
    | [_], h => simp [certPrime] at h

lemma certCof_sound {R : ℕ} {l l' : List ℕ} (h : certCof R l = some l') : R = 1 ∨ R.Prime := by
  unfold certCof at h
  split_ifs at h with h1
  · exact Or.inl (by simpa using h1)
  · exact Or.inr (certPrime_sound _ _ _ _ h)

/-! ### Soundness of member certificates -/

lemma not_primRoot_of_pow {p : ℕ} {x : ZMod p} {e : ℕ} (he : 0 < e) (hlt : e < p - 1)
    (h : x ^ e = 1) : orderOf x ≠ p - 1 := by
  have := orderOf_le_of_pow_eq_one he h
  omega

lemma member_sound {p w : ℕ} {ss : List ℕ} (hR : cofactor (p - 1) ss = 1 ∨
    (cofactor (p - 1) ss).Prime) (h : memberOK p w ss (cofactor (p - 1) ss) = true) :
    IsLNPR (-3) p := by
  simp only [memberOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h5, hss⟩, hluc⟩, hneg2⟩ := h
  obtain ⟨hp, hord⟩ := lucas_sound (fun s hs => smallPrime_prime (hss s hs)) hR hluc
  have : Fact p.Prime := ⟨hp⟩
  have hm3 : ((-3 : ℤ) : ZMod p) = ((p - 3 : ℕ) : ZMod p) := by
    have := cast_neg_int (q := p) (c := 3) (by omega); push_cast at this ⊢; exact this
  have hm2 : ((-2 : ℤ) : ZMod p) = ((p - 2 : ℕ) : ZMod p) := by
    have := cast_neg_int (q := p) (c := 2) (by omega); push_cast at this ⊢; exact this
  refine ⟨hp, by rw [IsPrimRoot, hm3]; exact hord, ?_⟩
  intro b hb1 hb2
  have hb : b = -2 ∨ b = -1 := by omega
  unfold IsPrimRoot
  rcases hb with rfl | rfl
  · rw [hm2]
    unfold negTwoOK at hneg2
    split_ifs at hneg2 with hw
    · -- `-2` is a square
      simp only [Bool.or_eq_true, beq_iff_eq] at hneg2
      obtain ⟨y, hy⟩ := (ZMod.exists_sq_eq_neg_two_iff (p := p) (by omega)).2 hneg2
      have hy0 : y ≠ 0 := by
        rintro rfl
        have h2 : ((2 : ℕ) : ZMod p) = 0 := by
          have := hy; simp only [mul_zero, neg_eq_zero] at this; exact_mod_cast this
        rw [ZMod.natCast_eq_zero_iff] at h2
        have := Nat.le_of_dvd (by norm_num) h2; omega
      have hodd : (p - 1) / 2 * 2 = p - 1 := by
        rcases hneg2 with h | h <;> omega
      refine not_primRoot_of_pow (e := (p - 1) / 2) (by omega) (by omega) ?_
      rw [← hm2]; push_cast
      rw [hy, ← pow_two, ← pow_mul, mul_comm, hodd]
      exact ZMod.pow_card_sub_one_eq_one hy0
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hneg2
      obtain ⟨⟨hw2, hwd⟩, hpow⟩ := hneg2
      have hdvd : w ∣ p - 1 := Nat.dvd_of_mod_eq_zero hwd
      have hpos : 0 < (p - 1) / w := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega)
      refine not_primRoot_of_pow hpos (Nat.div_lt_self (by omega) (by omega)) ?_
      rw [zmod_pow_eq, hpow, Nat.cast_one]
  · refine not_primRoot_of_pow (e := 2) (by omega) (by omega) ?_
    push_cast; ring

/-- An accepted member stream gives a lower bound for the counting function. -/
lemma run_sound : ∀ f nxt cnt l nxt' cnt', run f nxt cnt l = some (nxt', cnt') →
    Nat.count (IsLNPR (-3)) nxt + cnt' ≤ Nat.count (IsLNPR (-3)) nxt' + cnt := by
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
    | [_], h => simp [run] at h
    | [_, _], h => simp [run] at h
    | d :: w :: k :: l, h =>
      simp only [run] at h
      split_ifs at h with h1
      split at h
      · rename_i l' hc
        have hmem := member_sound (certCof_sound hc) h1
        have := ih _ _ _ _ _ h
        have hmono := Nat.count_monotone (IsLNPR (-3)) (Nat.le_add_right nxt d)
        simp only [Nat.count_succ, hmem, ite_true] at this
        omega
      · simp at h

/-- `run_sound` for a stream started with count 0. -/
lemma run_sound0 {f nxt nxt' c : ℕ} {l : List ℕ} (h : run f nxt 0 l = some (nxt', c)) :
    Nat.count (IsLNPR (-3)) nxt + c ≤ Nat.count (IsLNPR (-3)) nxt' :=
  run_sound f nxt 0 l nxt' c h

/-- An accepted gap stream shows that the range contains no member. -/
lemma runGap_sound : ∀ f nxt l nxt', runGap f nxt l = some nxt' →
    Nat.count (IsLNPR (-3)) nxt' = Nat.count (IsLNPR (-3)) nxt := by
  intro f
  induction f with
  | zero =>
    intro nxt l nxt' h
    match l, h with
    | [], h => simp only [runGap, Option.some.injEq] at h; rw [h]
    | _ :: _, h => simp [runGap] at h
  | succ f ih =>
    intro nxt l nxt' h
    have step : ∀ l₀, ¬ IsLNPR (-3) nxt → runGap f (nxt + 1) l₀ = some nxt' →
        Nat.count (IsLNPR (-3)) nxt' = Nat.count (IsLNPR (-3)) nxt := by
      intro l₀ hn hr
      rw [ih _ _ _ hr]
      simp [Nat.count_succ, hn]
    match l, h with
    | [], h => simp only [runGap, Option.some.injEq] at h; rw [h]
    | [_], h => simp [runGap] at h
    | 0 :: d :: l, h =>
      simp only [runGap] at h
      split_ifs at h with h1
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
      refine step _ ?_ h
      rintro ⟨hp, -⟩
      rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero h1.2) with h' | h' <;> omega
    | 1 :: w :: l, h =>
      simp only [runGap] at h
      split_ifs at h with h1
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
      obtain ⟨⟨⟨h5, hw2⟩, hwd⟩, hpow⟩ := h1
      refine step _ ?_ h
      rintro ⟨-, hroot, -⟩
      have hdvd : w ∣ nxt - 1 := Nat.dvd_of_mod_eq_zero hwd
      have hpos : 0 < (nxt - 1) / w := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega)
      refine not_primRoot_of_pow hpos (Nat.div_lt_self (by omega) (by omega)) ?_ hroot
      have hm3 : ((-3 : ℤ) : ZMod nxt) = ((nxt - 3 : ℕ) : ZMod nxt) := by
        have := cast_neg_int (q := nxt) (c := 3) (by omega); push_cast at this ⊢; exact this
      rw [hm3, zmod_pow_eq, hpow, Nat.cast_one]
    | 2 :: k :: l, h =>
      simp only [runGap] at h
      split_ifs at h with h1
      split at h
      · rename_i l' hc
        simp only [Bool.and_eq_true, List.all_eq_true] at h1
        obtain ⟨-, hord⟩ := lucas_sound (fun s hs => smallPrime_prime (h1.1 s hs))
          (certCof_sound hc) h1.2
        refine step _ ?_ h
        rintro ⟨-, -, hno⟩
        apply hno (-2) (by norm_num) (by norm_num)
        unfold IsPrimRoot
        have hm2 : ((-2 : ℤ) : ZMod nxt) = ((nxt - 2 : ℕ) : ZMod nxt) := by
          have h3 : 2 ≤ nxt := by
            have := lucasOK_three h1.2; omega
          have := cast_neg_int (q := nxt) (c := 2) h3; push_cast at this ⊢; exact this
        rw [hm2]; exact hord
      · simp at h
    | (_ + 3) :: _ :: _, h => simp [runGap] at h

end PrimRoot
