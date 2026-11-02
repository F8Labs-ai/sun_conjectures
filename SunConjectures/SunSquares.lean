import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
Sun, arXiv:1402.6641v12, Conjecture 2.14(ii): the sequence π(n²)^(1/n)
(n = 3, 4, …) is strictly decreasing.

Unconditional. For n ≥ 1000 the analytic input is Mathlib's Chebyshev bound
`Chebyshev.pi_ge_of_four_le`, combined with a mod-210 wheel bound for the primes
in (n², (n+1)²]. For 3 ≤ n < 1000 a checker evaluated by the kernel walks
through a table of the values π(n²); above 1000 the primes are counted as the
numbers coprime to 1000!. No external mathematical hypotheses.
-/

set_option autoImplicit false

namespace SunSquares

/-! ### Analytic part: n ≥ 1000 -/

lemma wheel_210 (n : ℕ) (hn : 15 ≤ n) :
    Nat.primeCounting ((n + 1) ^ 2) ≤
      Nat.primeCounting (n ^ 2) + 48 * ((2 * n + 1) / 210 + 1) := by
  have h := Nat.primeCounting'_add_le (a := 210) (k := n ^ 2 + 1) (by norm_num)
    (by nlinarith) (2 * n + 1)
  rw [show Nat.totient 210 = 48 by decide,
    show n ^ 2 + 1 + (2 * n + 1) = (n + 1) ^ 2 + 1 by ring] at h
  simpa only [Nat.primeCounting_eq_primeCounting'_succ] using h

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

lemma large_log_bound (n : ℕ) (hn : 1000 ≤ n) :
    (n : ℝ) * ((48 * ((2 * n + 1) / 210 + 1) : ℕ) : ℝ) <
      (Nat.primeCounting (n ^ 2) : ℝ) * Real.log (Nat.primeCounting (n ^ 2)) := by
  have hnr : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hcheb := Chebyshev.pi_ge_of_four_le (n := n ^ 2) (by nlinarith)
  set x : ℝ := ((n ^ 2 : ℕ) : ℝ) with hxdef
  set A : ℝ := (Nat.primeCounting (n ^ 2) : ℝ) with hAdef
  have hx : x = (n : ℝ) ^ 2 := by rw [hxdef]; push_cast; ring
  have hx19 : (2 : ℝ) ^ 19 ≤ x := by rw [hx]; nlinarith
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx19
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  set t : ℝ := Real.log x with htdef
  have ht : 19 * Real.log 2 ≤ t := by
    have h := Real.log_le_log (by positivity) hx19
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  have htlow : (1316 / 100 : ℝ) < t := by linarith
  have htpos : 0 < t := by linarith
  -- Chebyshev: A ≥ log 2 · x / t
  set u : ℝ := x / t with hudef
  have hupos : 0 < u := div_pos hxpos htpos
  have hxu : x = t * u := by rw [hudef]; field_simp
  have hu_le : u ≤ x / (1316 / 100) :=
    div_le_div_of_nonneg_left hxpos.le (by norm_num) htlow.le
  have ha : Real.log 2 * u ≤ A := by
    have e : x * Real.log 2 / t = Real.log 2 * u := by rw [hudef]; ring
    rw [← e]; exact hcheb
  have hapos : 0 < Real.log 2 * u := by positivity
  -- log A ≥ (15/16) t - 2.2155
  have hlogA : Real.log (Real.log 2 * u) ≤ Real.log A := Real.log_le_log hapos ha
  have hsplit : Real.log (Real.log 2 * u) = Real.log (Real.log 2) + t - Real.log t := by
    rw [Real.log_mul (by positivity) (ne_of_gt hupos), hudef,
      Real.log_div (ne_of_gt hxpos) (ne_of_gt htpos)]
    ring
  have hll2 : -(4429 / 10000 : ℝ) ≤ Real.log (Real.log 2) := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < Real.log 2 by positivity)
    have hinv : (Real.log 2)⁻¹ ≤ 14429 / 10000 := by
      have hm := mul_inv_cancel₀ (ne_of_gt (show 0 < Real.log 2 by positivity))
      have hip : 0 < (Real.log 2)⁻¹ := by positivity
      nlinarith [mul_le_mul_of_nonneg_right (le_of_lt hl2) hip.le]
    linarith
  have hlogt : Real.log t ≤ t / 16 + 4 * Real.log 2 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < t / 16 by positivity)
    rw [Real.log_div (ne_of_gt htpos) (by norm_num)] at h
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    linarith
  have hL : (15 / 16 : ℝ) * t - 22155 / 10000 ≤ Real.log A := by linarith
  have hLpos : 0 < (15 / 16 : ℝ) * t - 22155 / 10000 := by linarith
  -- A log A ≥ 0.533 x
  have hprod : Real.log 2 * u * ((15 / 16 : ℝ) * t - 22155 / 10000) ≤ A * Real.log A :=
    mul_le_mul ha hL hLpos.le (le_trans hapos.le ha)
  have hlow : (533 / 1000 : ℝ) * x ≤ Real.log 2 * u * ((15 / 16 : ℝ) * t - 22155 / 10000) := by
    have e : Real.log 2 * u * ((15 / 16 : ℝ) * t - 22155 / 10000) =
        Real.log 2 * ((15 / 16 : ℝ) * x - 22155 / 10000 * u) := by rw [hxu]; ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hu_le (show (0 : ℝ) ≤ 22155 / 10000 by norm_num)]
  -- the wheel term is at most 0.506 x
  have hdiv : (((2 * n + 1) / 210 : ℕ) : ℝ) ≤ (2 * (n : ℝ) + 1) / 210 := by
    have h := Nat.cast_div_le (α := ℝ) (m := 2 * n + 1) (n := 210)
    push_cast at h
    exact h
  have hc : (n : ℝ) * ((48 * ((2 * n + 1) / 210 + 1) : ℕ) : ℝ) ≤ (506 / 1000 : ℝ) * x := by
    push_cast
    rw [hx]
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hdiv hn0]
  linarith

theorem large_case (n : ℕ) (hn : 1000 ≤ n) :
    Nat.primeCounting ((n + 1) ^ 2) ^ n < Nat.primeCounting (n ^ 2) ^ (n + 1) := by
  have hA : 0 < (Nat.primeCounting (n ^ 2) : ℝ) := by
    exact_mod_cast pc_pos _ (by nlinarith)
  have hB : 0 < (Nat.primeCounting ((n + 1) ^ 2) : ℝ) := by
    exact_mod_cast pc_pos _ (by nlinarith)
  have hw := wheel_210 n (by omega)
  have hgrowth : (n : ℝ) * ((Nat.primeCounting ((n + 1) ^ 2) : ℝ) -
      (Nat.primeCounting (n ^ 2) : ℝ)) ≤
      (n : ℝ) * ((48 * ((2 * n + 1) / 210 + 1) : ℕ) : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h : (Nat.primeCounting ((n + 1) ^ 2) : ℝ) ≤ (Nat.primeCounting (n ^ 2) : ℝ) +
        ((48 * ((2 * n + 1) / 210 + 1) : ℕ) : ℝ) := by exact_mod_cast hw
    linarith
  have hlog := analytic_step n _ _ _ (by positivity) hA hB (large_log_bound n hn) hgrowth
  have hpow : (Nat.primeCounting ((n + 1) ^ 2) : ℝ) ^ n <
      (Nat.primeCounting (n ^ 2) : ℝ) ^ (n + 1) := by
    apply (Real.log_lt_log_iff (pow_pos hB _) (pow_pos hA _)).1
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using hlog
  exact_mod_cast hpow

/-! ### Kernel-checked part: 3 ≤ n < 1000 -/

/-- `chk p n (A₀ :: A₁ :: …)` checks, for consecutive entries, that `A_{i+1}` equals `A_i` plus
the number of `j ∈ ((n+i)², (n+i+1)²]` satisfying `p`, and that
`A_{i+1} ^ (n+i) < A_i ^ (n+i+1)`. -/
def chk (p : ℕ → Prop) [DecidablePred p] : ℕ → List ℕ → Bool
  | n, A :: B :: rest =>
      (B == A + Nat.count (fun j => p (n ^ 2 + 1 + j)) (2 * n + 1)) &&
        (decide (B ^ n < A ^ (n + 1)) && chk p (n + 1) (B :: rest))
  | _, _ => true

lemma count_congr_shift {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] (s L : ℕ)
    (h : ∀ j < L, (p (s + j) ↔ q (s + j))) :
    Nat.count (fun j => p (s + j)) L = Nat.count (fun j => q (s + j)) L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.count_succ, Nat.count_succ, ih (fun j hj => h j (by omega))]
    simp only [h L (by omega)]

lemma pc_sq_succ (n : ℕ) :
    Nat.primeCounting ((n + 1) ^ 2) = Nat.primeCounting (n ^ 2) +
      Nat.count (fun j => Nat.Prime (n ^ 2 + 1 + j)) (2 * n + 1) := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [show (n + 1) ^ 2 + 1 = (n ^ 2 + 1) + (2 * n + 1) by ring, Nat.count_add]

/-- One step of `chk`: the next table entry is the true value, and the inequality holds. -/
lemma chk_step (p : ℕ → Prop) [DecidablePred p] (n A B : ℕ) (rest : List ℕ)
    (hchk : chk p n (A :: B :: rest) = true) (hA : Nat.primeCounting (n ^ 2) = A)
    (hp : ∀ j, n ^ 2 < j → j ≤ (n + 1) ^ 2 → (p j ↔ Nat.Prime j)) :
    Nat.primeCounting ((n + 1) ^ 2) = B ∧ B ^ n < A ^ (n + 1) ∧
      chk p (n + 1) (B :: rest) = true := by
  simp only [chk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
  obtain ⟨hB, hpow, hrest⟩ := hchk
  have hcount : Nat.count (fun j => p (n ^ 2 + 1 + j)) (2 * n + 1) =
      Nat.count (fun j => Nat.Prime (n ^ 2 + 1 + j)) (2 * n + 1) :=
    count_congr_shift _ _ (fun j hj => hp _ (by omega) (by nlinarith))
  exact ⟨by rw [pc_sq_succ, hA, ← hcount, hB], hpow, hrest⟩

/-- Soundness of `chk`: if the table starts at the true value `π(n²)` and `p` agrees with
primality on the scanned range, every checked inequality holds. -/
lemma chk_sound (p : ℕ → Prop) [DecidablePred p] :
    ∀ (l : List ℕ) (n A : ℕ), chk p n (A :: l) = true → Nat.primeCounting (n ^ 2) = A →
      (∀ j, n ^ 2 < j → j ≤ (n + l.length) ^ 2 → (p j ↔ Nat.Prime j)) →
      ∀ m, n ≤ m → m < n + l.length →
        Nat.primeCounting ((m + 1) ^ 2) ^ m < Nat.primeCounting (m ^ 2) ^ (m + 1) := by
  intro l
  induction l with
  | nil => intro n A _ _ _ m h1 h2; simp at h2; omega
  | cons B rest ih =>
    intro n A hchk hA hp m h1 h2
    simp only [List.length_cons] at hp h2
    obtain ⟨hB', hpow, hrest⟩ :=
      chk_step p n A B rest hchk hA
        (fun j hj1 hj2 => hp j hj1 (le_trans hj2 (Nat.pow_le_pow_left (by omega) 2)))
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · rw [hB', hA]; exact hpow
    · exact ih (n + 1) B hrest hB'
        (fun j hj1 hj2 => hp j (by nlinarith) (by
          have e : n + 1 + rest.length = n + (rest.length + 1) := by ring
          rw [e] at hj2; exact hj2))
        m (by omega) (by omega)

/-- `chk` also certifies the last table entry, so that tables can be checked in pieces. -/
lemma chk_last (p : ℕ → Prop) [DecidablePred p] :
    ∀ (l : List ℕ) (n A Z : ℕ), chk p n (A :: l) = true → Nat.primeCounting (n ^ 2) = A →
      (∀ j, n ^ 2 < j → j ≤ (n + l.length) ^ 2 → (p j ↔ Nat.Prime j)) →
      (A :: l).getLast? = some Z → Nat.primeCounting ((n + l.length) ^ 2) = Z := by
  intro l
  induction l with
  | nil =>
    intro n A Z _ hA _ hZ
    simp only [List.getLast?_singleton, Option.some.injEq] at hZ
    simp only [List.length_nil, Nat.add_zero]
    rw [hA, hZ]
  | cons B rest ih =>
    intro n A Z hchk hA hp hZ
    simp only [List.length_cons] at hp ⊢
    obtain ⟨hB', -, hrest⟩ :=
      chk_step p n A B rest hchk hA
        (fun j hj1 hj2 => hp j hj1 (le_trans hj2 (Nat.pow_le_pow_left (by omega) 2)))
    rw [List.getLast?_cons_cons] at hZ
    have e : n + (rest.length + 1) = n + 1 + rest.length := by ring
    rw [e]
    exact ih (n + 1) B Z hrest hB' (fun j hj1 hj2 => hp j (by nlinarith) (by rw [e]; exact hj2)) hZ

/-- 1000! as a literal, so that the kernel reads it instead of recomputing it. -/
def F : ℕ := 402387260077093773543702433923003985719374864210714632543799910429938512398629020592044208486969404800479988610197196058631666872994808558901323829669944590997424504087073759918823627727188732519779505950995276120874975462497043601418278094646496291056393887437886487337119181045825783647849977012476632889835955735432513185323958463075557409114262417474349347553428646576611667797396668820291207379143853719588249808126867838374559731746136085379534524221586593201928090878297308431392844403281231558611036976801357304216168747609675871348312025478589320767169132448426236131412508780208000261683151027341827977704784635868170164365024153691398281264810213092761244896359928705114964975419909342221566832572080821333186116811553615836546984046708975602900950537616475847728421889679646244945160765353408198901385442487984959953319101723355556602139450399736280750137837615307127761926849034352625200015888535147331611702103968175921510907788019393178114194545257223865541461062892187960223838971476088506276862967146674697562911234082439208160153780889893964518263243671616762179168909779911903754031274622289988005195444414282012187361745992642956581746628302955570299024324153181617210465832036786906117260158783520751516284225540265170483304226143974286933061690897968482590125458327168226458066526769958652682272807075781391858178889652208164348344825993266043367660176999612831860788386150279465955131156552036093988180612138558600301435694527224206344631797460594682573103790084024432438465657245014402821885252470935190620929023136493273497565513958720559654228749774011413346962715422845862377387538230483865688976461927383814900140767310446640259899490222221765904339901886018566526485061799702356193897017860040811889729918311021171229845901641921068884387121855646124960798722908519296819372388642614839657382291123125024186649353143970137428531926649875337218940694281434118520158014123344828015051399694290153483077644569099073152433278288269864602789864321139083506217095002597389863554277196742822248757586765752344220207573630569498825087968928162753848863396909959826280956121450994871701244516461260379029309120889086942028510640182154399457156805941872748998094254742173582401063677404595741785160829230135358081840096996372524230560855903700624271243416909004153690105933983835777939410970027753472000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

lemma F_eq : F = Nat.factorial 1000 := by decide +kernel

lemma coprime_F_iff (j : ℕ) (h1 : 1000 < j) (h2 : j ≤ 1000000) :
    Nat.Coprime j F ↔ Nat.Prime j := by
  constructor
  · intro hc
    by_contra hp
    have hsq := Nat.minFac_sq_le_self (by omega) hp
    have hmf : Nat.minFac j ≤ 1000 := by nlinarith
    have hd : Nat.minFac j ∣ F := F_eq ▸ Nat.dvd_factorial (Nat.minFac_pos j) hmf
    have h1' : Nat.minFac j = 1 := by
      have hg := Nat.dvd_gcd (Nat.minFac_dvd j) hd
      rwa [Nat.Coprime.gcd_eq_one hc, Nat.dvd_one] at hg
    rw [Nat.minFac_eq_one_iff] at h1'
    omega
  · intro hp
    have hnd : ¬ j ∣ Nat.factorial 1000 := by rw [hp.dvd_factorial]; omega
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 (F_eq ▸ hnd)

lemma hp_range (n : ℕ) (l : List ℕ) (hn : 32 ≤ n) (hk : n + l.length ≤ 1000) :
    ∀ j, n ^ 2 < j → j ≤ (n + l.length) ^ 2 → (Nat.Coprime j F ↔ Nat.Prime j) := by
  intro j h1 h2
  have h3 := Nat.pow_le_pow_left hk 2
  exact coprime_F_iff j (by nlinarith) (by omega)

/-- π(n²) for n = 4, …, 32. -/
def L1 : List ℕ := [6, 9, 11, 15, 18, 22, 25, 30, 34, 39, 44, 48,
  54, 61, 66, 72, 78, 85, 92, 99, 105, 114, 122, 129,
  137, 146, 154, 162, 172]

-- The kernel evaluates primality through `Nat.decidablePrime'` (via `minFac`), which is much
-- faster there than the default instance.

lemma pc_9 : Nat.primeCounting (3 ^ 2) = 4 := by
  show Nat.count Nat.Prime 10 = 4
  rw [Nat.decidablePrime_csimp]
  decide +kernel

lemma pc_32 : Nat.primeCounting (32 ^ 2) = 172 := by
  show Nat.count Nat.Prime 1025 = 172
  rw [Nat.decidablePrime_csimp]
  decide +kernel

set_option maxRecDepth 100000 in
lemma L1_ok : @chk Nat.Prime Nat.decidablePrime' 3 (4 :: L1) = true := by decide +kernel

lemma L1_length : L1.length = 29 := by rfl

/-! The range 32 ≤ n ≤ 1000 is checked in chunks of 30 steps, so that each kernel check
stays small; `chk_last` carries the value of π(n²) from one chunk to the next. -/

/-- π(n²) for n = 33, …, 62. -/
def C0 : List ℕ := [181, 191, 200, 210, 219, 228, 240, 251, 263, 274, 283, 295,
  306, 319, 329, 342, 357, 367, 378, 393, 409, 421, 434, 445,
  457, 474, 487, 503, 519, 532]

lemma C0_length : C0.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C0_ok : chk (fun j => Nat.Coprime j F) 32 (172 :: C0) = true := by decide +kernel

lemma pc_62 : Nat.primeCounting (62 ^ 2) = 532 := by
  have h := chk_last _ C0 32 172 532 C0_ok pc_32 (hp_range 32 C0 (by norm_num) (by rw [C0_length]; norm_num)) (by rfl)
  rwa [C0_length] at h

/-- π(n²) for n = 63, …, 92. -/
def C1 : List ℕ := [549, 564, 578, 594, 609, 624, 641, 654, 675, 690, 705, 722,
  739, 757, 779, 793, 811, 834, 847, 867, 886, 906, 923, 939,
  960, 982, 1000, 1018, 1038, 1058]

lemma C1_length : C1.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C1_ok : chk (fun j => Nat.Coprime j F) 62 (532 :: C1) = true := by decide +kernel

lemma pc_92 : Nat.primeCounting (92 ^ 2) = 1058 := by
  have h := chk_last _ C1 62 532 1058 C1_ok pc_62 (hp_range 62 C1 (by norm_num) (by rw [C1_length]; norm_num)) (by rfl)
  rwa [C1_length] at h

/-- π(n²) for n = 93, …, 122. -/
def C2 : List ℕ := [1077, 1100, 1121, 1142, 1163, 1185, 1208, 1229, 1252, 1274, 1294, 1315,
  1336, 1357, 1381, 1400, 1423, 1447, 1471, 1498, 1523, 1547, 1572, 1594,
  1617, 1646, 1667, 1686, 1715, 1743]

lemma C2_length : C2.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C2_ok : chk (fun j => Nat.Coprime j F) 92 (1058 :: C2) = true := by decide +kernel

lemma pc_122 : Nat.primeCounting (122 ^ 2) = 1743 := by
  have h := chk_last _ C2 92 1058 1743 C2_ok pc_92 (hp_range 92 C2 (by norm_num) (by rw [C2_length]; norm_num)) (by rfl)
  rwa [C2_length] at h

/-- π(n²) for n = 123, …, 152. -/
def C3 : List ℕ := [1766, 1796, 1821, 1848, 1877, 1900, 1924, 1948, 1976, 2004, 2032, 2057,
  2088, 2118, 2141, 2163, 2190, 2223, 2248, 2281, 2310, 2334, 2366, 2392,
  2426, 2456, 2489, 2515, 2547, 2580]

lemma C3_length : C3.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C3_ok : chk (fun j => Nat.Coprime j F) 122 (1743 :: C3) = true := by decide +kernel

lemma pc_152 : Nat.primeCounting (152 ^ 2) = 2580 := by
  have h := chk_last _ C3 122 1743 2580 C3_ok pc_122 (hp_range 122 C3 (by norm_num) (by rw [C3_length]; norm_num)) (by rfl)
  rwa [C3_length] at h

/-- π(n²) for n = 153, …, 182. -/
def C4 : List ℕ := [2607, 2637, 2672, 2702, 2729, 2757, 2788, 2818, 2851, 2883, 2915, 2951,
  2980, 3010, 3043, 3076, 3107, 3145, 3178, 3211, 3241, 3274, 3302, 3338,
  3377, 3407, 3436, 3476, 3512, 3551]

lemma C4_length : C4.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C4_ok : chk (fun j => Nat.Coprime j F) 152 (2580 :: C4) = true := by decide +kernel

lemma pc_182 : Nat.primeCounting (182 ^ 2) = 3551 := by
  have h := chk_last _ C4 152 2580 3551 C4_ok pc_152 (hp_range 152 C4 (by norm_num) (by rw [C4_length]; norm_num)) (by rfl)
  rwa [C4_length] at h

/-- π(n²) for n = 183, …, 212. -/
def C5 : List ℕ := [3585, 3625, 3656, 3695, 3731, 3765, 3795, 3834, 3868, 3908, 3945, 3986,
  4018, 4052, 4089, 4127, 4164, 4203, 4236, 4271, 4313, 4352, 4396, 4436,
  4480, 4515, 4551, 4589, 4627, 4669]

lemma C5_length : C5.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C5_ok : chk (fun j => Nat.Coprime j F) 182 (3551 :: C5) = true := by decide +kernel

lemma pc_212 : Nat.primeCounting (212 ^ 2) = 4669 := by
  have h := chk_last _ C5 182 3551 4669 C5_ok pc_182 (hp_range 182 C5 (by norm_num) (by rw [C5_length]; norm_num)) (by rfl)
  rwa [C5_length] at h

/-- π(n²) for n = 213, …, 242. -/
def C6 : List ℕ := [4707, 4743, 4781, 4821, 4857, 4899, 4942, 4978, 5022, 5065, 5106, 5152,
  5191, 5229, 5274, 5318, 5356, 5397, 5442, 5483, 5522, 5570, 5611, 5652,
  5698, 5743, 5792, 5835, 5882, 5926]

lemma C6_length : C6.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C6_ok : chk (fun j => Nat.Coprime j F) 212 (4669 :: C6) = true := by decide +kernel

lemma pc_242 : Nat.primeCounting (242 ^ 2) = 5926 := by
  have h := chk_last _ C6 212 4669 5926 C6_ok pc_212 (hp_range 212 C6 (by norm_num) (by rw [C6_length]; norm_num)) (by rfl)
  rwa [C6_length] at h

/-- π(n²) for n = 243, …, 272. -/
def C7 : List ℕ := [5968, 6018, 6059, 6101, 6147, 6186, 6232, 6275, 6320, 6365, 6414, 6454,
  6495, 6542, 6595, 6636, 6684, 6735, 6783, 6823, 6869, 6910, 6960, 7007,
  7057, 7108, 7161, 7206, 7252, 7300]

lemma C7_length : C7.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C7_ok : chk (fun j => Nat.Coprime j F) 242 (5926 :: C7) = true := by decide +kernel

lemma pc_272 : Nat.primeCounting (272 ^ 2) = 7300 := by
  have h := chk_last _ C7 242 5926 7300 C7_ok pc_242 (hp_range 242 C7 (by norm_num) (by rw [C7_length]; norm_num)) (by rfl)
  rwa [C7_length] at h

/-- π(n²) for n = 273, …, 302. -/
def C8 : List ℕ := [7351, 7399, 7450, 7499, 7544, 7594, 7650, 7694, 7743, 7789, 7842, 7891,
  7950, 7999, 8053, 8103, 8152, 8198, 8251, 8303, 8354, 8405, 8452, 8506,
  8555, 8600, 8657, 8713, 8769, 8821]

lemma C8_length : C8.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C8_ok : chk (fun j => Nat.Coprime j F) 272 (7300 :: C8) = true := by decide +kernel

lemma pc_302 : Nat.primeCounting (302 ^ 2) = 8821 := by
  have h := chk_last _ C8 272 7300 8821 C8_ok pc_272 (hp_range 272 C8 (by norm_num) (by rw [C8_length]; norm_num)) (by rfl)
  rwa [C8_length] at h

/-- π(n²) for n = 303, …, 332. -/
def C9 : List ℕ := [8870, 8928, 8985, 9041, 9089, 9147, 9205, 9260, 9309, 9361, 9416, 9466,
  9525, 9580, 9631, 9685, 9745, 9805, 9855, 9907, 9964, 10022, 10077, 10127,
  10191, 10238, 10298, 10353, 10415, 10466]

lemma C9_length : C9.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C9_ok : chk (fun j => Nat.Coprime j F) 302 (8821 :: C9) = true := by decide +kernel

lemma pc_332 : Nat.primeCounting (332 ^ 2) = 10466 := by
  have h := chk_last _ C9 302 8821 10466 C9_ok pc_302 (hp_range 302 C9 (by norm_num) (by rw [C9_length]; norm_num)) (by rfl)
  rwa [C9_length] at h

/-- π(n²) for n = 333, …, 362. -/
def C10 : List ℕ := [10523, 10580, 10639, 10690, 10756, 10811, 10867, 10921, 10987, 11041, 11098, 11159,
  11214, 11274, 11335, 11399, 11460, 11522, 11578, 11641, 11701, 11762, 11823, 11882,
  11936, 11998, 12064, 12131, 12187, 12248]

lemma C10_length : C10.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C10_ok : chk (fun j => Nat.Coprime j F) 332 (10466 :: C10) = true := by decide +kernel

lemma pc_362 : Nat.primeCounting (362 ^ 2) = 12248 := by
  have h := chk_last _ C10 332 10466 12248 C10_ok pc_332 (hp_range 332 C10 (by norm_num) (by rw [C10_length]; norm_num)) (by rfl)
  rwa [C10_length] at h

/-- π(n²) for n = 363, …, 392. -/
def C11 : List ℕ := [12307, 12366, 12433, 12490, 12553, 12613, 12677, 12751, 12813, 12873, 12934, 12997,
  13062, 13129, 13196, 13255, 13314, 13372, 13435, 13499, 13566, 13631, 13692, 13756,
  13829, 13895, 13960, 14034, 14100, 14164]

lemma C11_length : C11.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C11_ok : chk (fun j => Nat.Coprime j F) 362 (12248 :: C11) = true := by decide +kernel

lemma pc_392 : Nat.primeCounting (392 ^ 2) = 14164 := by
  have h := chk_last _ C11 362 12248 14164 C11_ok pc_362 (hp_range 362 C11 (by norm_num) (by rw [C11_length]; norm_num)) (by rfl)
  rwa [C11_length] at h

/-- π(n²) for n = 393, …, 422. -/
def C12 : List ℕ := [14228, 14293, 14360, 14420, 14490, 14552, 14615, 14683, 14752, 14818, 14877, 14951,
  15018, 15084, 15146, 15209, 15283, 15346, 15406, 15473, 15548, 15613, 15687, 15758,
  15823, 15894, 15953, 16030, 16104, 16165]

lemma C12_length : C12.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C12_ok : chk (fun j => Nat.Coprime j F) 392 (14164 :: C12) = true := by decide +kernel

lemma pc_422 : Nat.primeCounting (422 ^ 2) = 16165 := by
  have h := chk_last _ C12 392 14164 16165 C12_ok pc_392 (hp_range 392 C12 (by norm_num) (by rw [C12_length]; norm_num)) (by rfl)
  rwa [C12_length] at h

/-- π(n²) for n = 423, …, 452. -/
def C13 : List ℕ := [16242, 16318, 16393, 16449, 16522, 16594, 16667, 16735, 16813, 16886, 16964, 17027,
  17097, 17175, 17243, 17317, 17388, 17463, 17531, 17607, 17678, 17746, 17823, 17897,
  17969, 18038, 18108, 18185, 18259, 18324]

lemma C13_length : C13.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C13_ok : chk (fun j => Nat.Coprime j F) 422 (16165 :: C13) = true := by decide +kernel

lemma pc_452 : Nat.primeCounting (452 ^ 2) = 18324 := by
  have h := chk_last _ C13 422 16165 18324 C13_ok pc_422 (hp_range 422 C13 (by norm_num) (by rw [C13_length]; norm_num)) (by rfl)
  rwa [C13_length] at h

/-- π(n²) for n = 453, …, 482. -/
def C14 : List ℕ := [18399, 18475, 18549, 18627, 18707, 18784, 18866, 18942, 19012, 19084, 19157, 19231,
  19304, 19373, 19451, 19530, 19614, 19688, 19765, 19836, 19918, 19993, 20074, 20148,
  20224, 20301, 20385, 20476, 20548, 20621]

lemma C14_length : C14.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C14_ok : chk (fun j => Nat.Coprime j F) 452 (18324 :: C14) = true := by decide +kernel

lemma pc_482 : Nat.primeCounting (482 ^ 2) = 20621 := by
  have h := chk_last _ C14 452 18324 20621 C14_ok pc_452 (hp_range 452 C14 (by norm_num) (by rw [C14_length]; norm_num)) (by rfl)
  rwa [C14_length] at h

/-- π(n²) for n = 483, …, 512. -/
def C15 : List ℕ := [20694, 20768, 20851, 20919, 20997, 21068, 21150, 21231, 21310, 21395, 21470, 21549,
  21634, 21714, 21799, 21876, 21964, 22044, 22115, 22204, 22282, 22363, 22441, 22529,
  22599, 22679, 22765, 22845, 22925, 23000]

lemma C15_length : C15.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C15_ok : chk (fun j => Nat.Coprime j F) 482 (20621 :: C15) = true := by decide +kernel

lemma pc_512 : Nat.primeCounting (512 ^ 2) = 23000 := by
  have h := chk_last _ C15 482 20621 23000 C15_ok pc_482 (hp_range 482 C15 (by norm_num) (by rw [C15_length]; norm_num)) (by rfl)
  rwa [C15_length] at h

/-- π(n²) for n = 513, …, 542. -/
def C16 : List ℕ := [23079, 23168, 23247, 23332, 23415, 23511, 23594, 23676, 23760, 23849, 23925, 24000,
  24091, 24179, 24258, 24341, 24421, 24507, 24601, 24684, 24760, 24856, 24933, 25018,
  25089, 25182, 25267, 25356, 25438, 25516]

lemma C16_length : C16.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C16_ok : chk (fun j => Nat.Coprime j F) 512 (23000 :: C16) = true := by decide +kernel

lemma pc_542 : Nat.primeCounting (542 ^ 2) = 25516 := by
  have h := chk_last _ C16 512 23000 25516 C16_ok pc_512 (hp_range 512 C16 (by norm_num) (by rw [C16_length]; norm_num)) (by rfl)
  rwa [C16_length] at h

/-- π(n²) for n = 543, …, 572. -/
def C17 : List ℕ := [25602, 25684, 25775, 25855, 25936, 26020, 26112, 26193, 26290, 26380, 26476, 26565,
  26646, 26734, 26820, 26906, 26992, 27082, 27177, 27261, 27356, 27445, 27543, 27641,
  27729, 27820, 27903, 27996, 28092, 28176]

lemma C17_length : C17.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C17_ok : chk (fun j => Nat.Coprime j F) 542 (25516 :: C17) = true := by decide +kernel

lemma pc_572 : Nat.primeCounting (572 ^ 2) = 28176 := by
  have h := chk_last _ C17 542 25516 28176 C17_ok pc_542 (hp_range 542 C17 (by norm_num) (by rw [C17_length]; norm_num)) (by rfl)
  rwa [C17_length] at h

/-- π(n²) for n = 573, …, 602. -/
def C18 : List ℕ := [28274, 28361, 28453, 28546, 28632, 28725, 28818, 28904, 29001, 29096, 29178, 29269,
  29361, 29454, 29544, 29636, 29731, 29827, 29914, 30010, 30103, 30201, 30294, 30397,
  30482, 30568, 30667, 30757, 30835, 30940]

lemma C18_length : C18.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C18_ok : chk (fun j => Nat.Coprime j F) 572 (28176 :: C18) = true := by decide +kernel

lemma pc_602 : Nat.primeCounting (602 ^ 2) = 30940 := by
  have h := chk_last _ C18 572 28176 30940 C18_ok pc_572 (hp_range 572 C18 (by norm_num) (by rw [C18_length]; norm_num)) (by rfl)
  rwa [C18_length] at h

/-- π(n²) for n = 603, …, 632. -/
def C19 : List ℕ := [31033, 31126, 31221, 31324, 31417, 31497, 31587, 31675, 31774, 31864, 31973, 32069,
  32157, 32255, 32349, 32442, 32538, 32637, 32736, 32830, 32917, 33013, 33118, 33216,
  33326, 33427, 33525, 33613, 33713, 33813]

lemma C19_length : C19.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C19_ok : chk (fun j => Nat.Coprime j F) 602 (30940 :: C19) = true := by decide +kernel

lemma pc_632 : Nat.primeCounting (632 ^ 2) = 33813 := by
  have h := chk_last _ C19 602 30940 33813 C19_ok pc_602 (hp_range 602 C19 (by norm_num) (by rw [C19_length]; norm_num)) (by rfl)
  rwa [C19_length] at h

/-- π(n²) for n = 633, …, 662. -/
def C20 : List ℕ := [33910, 33996, 34094, 34193, 34286, 34373, 34478, 34579, 34681, 34786, 34875, 34978,
  35083, 35174, 35278, 35383, 35483, 35578, 35684, 35787, 35880, 35977, 36075, 36183,
  36287, 36398, 36503, 36615, 36714, 36806]

lemma C20_length : C20.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C20_ok : chk (fun j => Nat.Coprime j F) 632 (33813 :: C20) = true := by decide +kernel

lemma pc_662 : Nat.primeCounting (662 ^ 2) = 36806 := by
  have h := chk_last _ C20 632 33813 36806 C20_ok pc_632 (hp_range 632 C20 (by norm_num) (by rw [C20_length]; norm_num)) (by rfl)
  rwa [C20_length] at h

/-- π(n²) for n = 663, …, 692. -/
def C21 : List ℕ := [36903, 37011, 37115, 37227, 37339, 37430, 37525, 37619, 37728, 37837, 37933, 38030,
  38136, 38236, 38337, 38442, 38538, 38629, 38734, 38853, 38950, 39053, 39164, 39275,
  39387, 39485, 39596, 39715, 39809, 39921]

lemma C21_length : C21.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C21_ok : chk (fun j => Nat.Coprime j F) 662 (36806 :: C21) = true := by decide +kernel

lemma pc_692 : Nat.primeCounting (692 ^ 2) = 39921 := by
  have h := chk_last _ C21 662 36806 39921 C21_ok pc_662 (hp_range 662 C21 (by norm_num) (by rw [C21_length]; norm_num)) (by rfl)
  rwa [C21_length] at h

/-- π(n²) for n = 693, …, 722. -/
def C22 : List ℕ := [40026, 40132, 40243, 40348, 40433, 40542, 40654, 40766, 40874, 40978, 41084, 41202,
  41306, 41412, 41527, 41643, 41737, 41840, 41957, 42065, 42169, 42275, 42385, 42486,
  42602, 42701, 42820, 42938, 43048, 43157]

lemma C22_length : C22.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C22_ok : chk (fun j => Nat.Coprime j F) 692 (39921 :: C22) = true := by decide +kernel

lemma pc_722 : Nat.primeCounting (722 ^ 2) = 43157 := by
  have h := chk_last _ C22 692 39921 43157 C22_ok pc_692 (hp_range 692 C22 (by norm_num) (by rw [C22_length]; norm_num)) (by rfl)
  rwa [C22_length] at h

/-- π(n²) for n = 723, …, 752. -/
def C23 : List ℕ := [43274, 43378, 43491, 43610, 43715, 43823, 43934, 44045, 44155, 44256, 44381, 44483,
  44588, 44699, 44813, 44921, 45030, 45137, 45251, 45364, 45481, 45589, 45704, 45805,
  45922, 46029, 46158, 46257, 46369, 46487]

lemma C23_length : C23.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C23_ok : chk (fun j => Nat.Coprime j F) 722 (43157 :: C23) = true := by decide +kernel

lemma pc_752 : Nat.primeCounting (752 ^ 2) = 46487 := by
  have h := chk_last _ C23 722 43157 46487 C23_ok pc_722 (hp_range 722 C23 (by norm_num) (by rw [C23_length]; norm_num)) (by rfl)
  rwa [C23_length] at h

/-- π(n²) for n = 753, …, 782. -/
def C24 : List ℕ := [46596, 46706, 46821, 46940, 47064, 47173, 47287, 47406, 47520, 47631, 47753, 47869,
  47982, 48100, 48233, 48340, 48446, 48561, 48680, 48801, 48916, 49030, 49145, 49262,
  49377, 49501, 49613, 49733, 49857, 49968]

lemma C24_length : C24.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C24_ok : chk (fun j => Nat.Coprime j F) 752 (46487 :: C24) = true := by decide +kernel

lemma pc_782 : Nat.primeCounting (782 ^ 2) = 49968 := by
  have h := chk_last _ C24 752 46487 49968 C24_ok pc_752 (hp_range 752 C24 (by norm_num) (by rw [C24_length]; norm_num)) (by rfl)
  rwa [C24_length] at h

/-- π(n²) for n = 783, …, 812. -/
def C25 : List ℕ := [50086, 50203, 50327, 50458, 50568, 50685, 50799, 50916, 51035, 51145, 51256, 51367,
  51489, 51609, 51730, 51854, 51967, 52074, 52192, 52306, 52431, 52553, 52676, 52798,
  52913, 53037, 53156, 53275, 53397, 53514]

lemma C25_length : C25.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C25_ok : chk (fun j => Nat.Coprime j F) 782 (49968 :: C25) = true := by decide +kernel

lemma pc_812 : Nat.primeCounting (812 ^ 2) = 53514 := by
  have h := chk_last _ C25 782 49968 53514 C25_ok pc_782 (hp_range 782 C25 (by norm_num) (by rw [C25_length]; norm_num)) (by rfl)
  rwa [C25_length] at h

/-- π(n²) for n = 813, …, 842. -/
def C26 : List ℕ := [53645, 53761, 53886, 54013, 54129, 54244, 54367, 54495, 54614, 54738, 54858, 54979,
  55114, 55234, 55356, 55477, 55602, 55729, 55851, 55969, 56100, 56222, 56350, 56465,
  56585, 56707, 56836, 56969, 57097, 57225]

lemma C26_length : C26.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C26_ok : chk (fun j => Nat.Coprime j F) 812 (53514 :: C26) = true := by decide +kernel

lemma pc_842 : Nat.primeCounting (842 ^ 2) = 57225 := by
  have h := chk_last _ C26 812 53514 57225 C26_ok pc_812 (hp_range 812 C26 (by norm_num) (by rw [C26_length]; norm_num)) (by rfl)
  rwa [C26_length] at h

/-- π(n²) for n = 843, …, 872. -/
def C27 : List ℕ := [57356, 57482, 57605, 57726, 57848, 57963, 58090, 58225, 58355, 58479, 58608, 58733,
  58858, 58986, 59113, 59248, 59372, 59502, 59622, 59746, 59862, 59981, 60105, 60236,
  60364, 60490, 60629, 60749, 60872, 61008]

lemma C27_length : C27.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C27_ok : chk (fun j => Nat.Coprime j F) 842 (57225 :: C27) = true := by decide +kernel

lemma pc_872 : Nat.primeCounting (872 ^ 2) = 61008 := by
  have h := chk_last _ C27 842 57225 61008 C27_ok pc_842 (hp_range 842 C27 (by norm_num) (by rw [C27_length]; norm_num)) (by rfl)
  rwa [C27_length] at h

/-- π(n²) for n = 873, …, 902. -/
def C28 : List ℕ := [61145, 61269, 61408, 61539, 61670, 61802, 61929, 62061, 62182, 62313, 62444, 62578,
  62705, 62838, 62968, 63105, 63229, 63363, 63498, 63632, 63768, 63894, 64040, 64162,
  64288, 64432, 64547, 64683, 64820, 64950]

lemma C28_length : C28.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C28_ok : chk (fun j => Nat.Coprime j F) 872 (61008 :: C28) = true := by decide +kernel

lemma pc_902 : Nat.primeCounting (902 ^ 2) = 64950 := by
  have h := chk_last _ C28 872 61008 64950 C28_ok pc_872 (hp_range 872 C28 (by norm_num) (by rw [C28_length]; norm_num)) (by rfl)
  rwa [C28_length] at h

/-- π(n²) for n = 903, …, 932. -/
def C29 : List ℕ := [65077, 65215, 65335, 65479, 65616, 65755, 65895, 66032, 66156, 66296, 66436, 66557,
  66692, 66824, 66950, 67090, 67230, 67353, 67488, 67626, 67761, 67886, 68018, 68163,
  68294, 68436, 68578, 68707, 68848, 68991]

lemma C29_length : C29.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C29_ok : chk (fun j => Nat.Coprime j F) 902 (64950 :: C29) = true := by decide +kernel

lemma pc_932 : Nat.primeCounting (932 ^ 2) = 68991 := by
  have h := chk_last _ C29 902 64950 68991 C29_ok pc_902 (hp_range 902 C29 (by norm_num) (by rw [C29_length]; norm_num)) (by rfl)
  rwa [C29_length] at h

/-- π(n²) for n = 933, …, 962. -/
def C30 : List ℕ := [69134, 69264, 69389, 69537, 69669, 69813, 69957, 70089, 70221, 70361, 70503, 70633,
  70774, 70913, 71052, 71194, 71319, 71454, 71583, 71727, 71879, 72035, 72170, 72291,
  72426, 72568, 72709, 72848, 72992, 73146]

lemma C30_length : C30.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C30_ok : chk (fun j => Nat.Coprime j F) 932 (68991 :: C30) = true := by decide +kernel

lemma pc_962 : Nat.primeCounting (962 ^ 2) = 73146 := by
  have h := chk_last _ C30 932 68991 73146 C30_ok pc_932 (hp_range 932 C30 (by norm_num) (by rw [C30_length]; norm_num)) (by rfl)
  rwa [C30_length] at h

/-- π(n²) for n = 963, …, 992. -/
def C31 : List ℕ := [73284, 73421, 73558, 73696, 73843, 73979, 74114, 74253, 74399, 74547, 74676, 74812,
  74953, 75096, 75236, 75374, 75506, 75647, 75795, 75943, 76082, 76223, 76366, 76520,
  76656, 76806, 76938, 77072, 77214, 77354]

lemma C31_length : C31.length = 30 := by rfl

set_option maxRecDepth 100000 in
lemma C31_ok : chk (fun j => Nat.Coprime j F) 962 (73146 :: C31) = true := by decide +kernel

lemma pc_992 : Nat.primeCounting (992 ^ 2) = 77354 := by
  have h := chk_last _ C31 962 73146 77354 C31_ok pc_962 (hp_range 962 C31 (by norm_num) (by rw [C31_length]; norm_num)) (by rfl)
  rwa [C31_length] at h

/-- π(n²) for n = 993, …, 1000. -/
def C32 : List ℕ := [77497, 77637, 77780, 77928, 78060, 78208, 78359, 78498]

lemma C32_length : C32.length = 8 := by rfl

set_option maxRecDepth 100000 in
lemma C32_ok : chk (fun j => Nat.Coprime j F) 992 (77354 :: C32) = true := by decide +kernel

lemma pc_1000 : Nat.primeCounting (1000 ^ 2) = 78498 := by
  have h := chk_last _ C32 992 77354 78498 C32_ok pc_992 (hp_range 992 C32 (by norm_num) (by rw [C32_length])) (by rfl)
  rwa [C32_length] at h

theorem finite_case (n : ℕ) (h1 : 3 ≤ n) (h2 : n < 1000) :
    Nat.primeCounting ((n + 1) ^ 2) ^ n < Nat.primeCounting (n ^ 2) ^ (n + 1) := by
  by_cases h : n < 32
  · exact @chk_sound Nat.Prime Nat.decidablePrime' L1 3 4 L1_ok pc_9 (fun _ _ _ => Iff.rfl)
      n h1 (by rw [L1_length]; omega)
  by_cases hc0 : n < 62
  · exact chk_sound _ C0 32 172 C0_ok pc_32
      (hp_range 32 C0 (by norm_num) (by rw [C0_length]; norm_num))
      n (by omega) (by rw [C0_length]; omega)
  by_cases hc1 : n < 92
  · exact chk_sound _ C1 62 532 C1_ok pc_62
      (hp_range 62 C1 (by norm_num) (by rw [C1_length]; norm_num))
      n (by omega) (by rw [C1_length]; omega)
  by_cases hc2 : n < 122
  · exact chk_sound _ C2 92 1058 C2_ok pc_92
      (hp_range 92 C2 (by norm_num) (by rw [C2_length]; norm_num))
      n (by omega) (by rw [C2_length]; omega)
  by_cases hc3 : n < 152
  · exact chk_sound _ C3 122 1743 C3_ok pc_122
      (hp_range 122 C3 (by norm_num) (by rw [C3_length]; norm_num))
      n (by omega) (by rw [C3_length]; omega)
  by_cases hc4 : n < 182
  · exact chk_sound _ C4 152 2580 C4_ok pc_152
      (hp_range 152 C4 (by norm_num) (by rw [C4_length]; norm_num))
      n (by omega) (by rw [C4_length]; omega)
  by_cases hc5 : n < 212
  · exact chk_sound _ C5 182 3551 C5_ok pc_182
      (hp_range 182 C5 (by norm_num) (by rw [C5_length]; norm_num))
      n (by omega) (by rw [C5_length]; omega)
  by_cases hc6 : n < 242
  · exact chk_sound _ C6 212 4669 C6_ok pc_212
      (hp_range 212 C6 (by norm_num) (by rw [C6_length]; norm_num))
      n (by omega) (by rw [C6_length]; omega)
  by_cases hc7 : n < 272
  · exact chk_sound _ C7 242 5926 C7_ok pc_242
      (hp_range 242 C7 (by norm_num) (by rw [C7_length]; norm_num))
      n (by omega) (by rw [C7_length]; omega)
  by_cases hc8 : n < 302
  · exact chk_sound _ C8 272 7300 C8_ok pc_272
      (hp_range 272 C8 (by norm_num) (by rw [C8_length]; norm_num))
      n (by omega) (by rw [C8_length]; omega)
  by_cases hc9 : n < 332
  · exact chk_sound _ C9 302 8821 C9_ok pc_302
      (hp_range 302 C9 (by norm_num) (by rw [C9_length]; norm_num))
      n (by omega) (by rw [C9_length]; omega)
  by_cases hc10 : n < 362
  · exact chk_sound _ C10 332 10466 C10_ok pc_332
      (hp_range 332 C10 (by norm_num) (by rw [C10_length]; norm_num))
      n (by omega) (by rw [C10_length]; omega)
  by_cases hc11 : n < 392
  · exact chk_sound _ C11 362 12248 C11_ok pc_362
      (hp_range 362 C11 (by norm_num) (by rw [C11_length]; norm_num))
      n (by omega) (by rw [C11_length]; omega)
  by_cases hc12 : n < 422
  · exact chk_sound _ C12 392 14164 C12_ok pc_392
      (hp_range 392 C12 (by norm_num) (by rw [C12_length]; norm_num))
      n (by omega) (by rw [C12_length]; omega)
  by_cases hc13 : n < 452
  · exact chk_sound _ C13 422 16165 C13_ok pc_422
      (hp_range 422 C13 (by norm_num) (by rw [C13_length]; norm_num))
      n (by omega) (by rw [C13_length]; omega)
  by_cases hc14 : n < 482
  · exact chk_sound _ C14 452 18324 C14_ok pc_452
      (hp_range 452 C14 (by norm_num) (by rw [C14_length]; norm_num))
      n (by omega) (by rw [C14_length]; omega)
  by_cases hc15 : n < 512
  · exact chk_sound _ C15 482 20621 C15_ok pc_482
      (hp_range 482 C15 (by norm_num) (by rw [C15_length]; norm_num))
      n (by omega) (by rw [C15_length]; omega)
  by_cases hc16 : n < 542
  · exact chk_sound _ C16 512 23000 C16_ok pc_512
      (hp_range 512 C16 (by norm_num) (by rw [C16_length]; norm_num))
      n (by omega) (by rw [C16_length]; omega)
  by_cases hc17 : n < 572
  · exact chk_sound _ C17 542 25516 C17_ok pc_542
      (hp_range 542 C17 (by norm_num) (by rw [C17_length]; norm_num))
      n (by omega) (by rw [C17_length]; omega)
  by_cases hc18 : n < 602
  · exact chk_sound _ C18 572 28176 C18_ok pc_572
      (hp_range 572 C18 (by norm_num) (by rw [C18_length]; norm_num))
      n (by omega) (by rw [C18_length]; omega)
  by_cases hc19 : n < 632
  · exact chk_sound _ C19 602 30940 C19_ok pc_602
      (hp_range 602 C19 (by norm_num) (by rw [C19_length]; norm_num))
      n (by omega) (by rw [C19_length]; omega)
  by_cases hc20 : n < 662
  · exact chk_sound _ C20 632 33813 C20_ok pc_632
      (hp_range 632 C20 (by norm_num) (by rw [C20_length]; norm_num))
      n (by omega) (by rw [C20_length]; omega)
  by_cases hc21 : n < 692
  · exact chk_sound _ C21 662 36806 C21_ok pc_662
      (hp_range 662 C21 (by norm_num) (by rw [C21_length]; norm_num))
      n (by omega) (by rw [C21_length]; omega)
  by_cases hc22 : n < 722
  · exact chk_sound _ C22 692 39921 C22_ok pc_692
      (hp_range 692 C22 (by norm_num) (by rw [C22_length]; norm_num))
      n (by omega) (by rw [C22_length]; omega)
  by_cases hc23 : n < 752
  · exact chk_sound _ C23 722 43157 C23_ok pc_722
      (hp_range 722 C23 (by norm_num) (by rw [C23_length]; norm_num))
      n (by omega) (by rw [C23_length]; omega)
  by_cases hc24 : n < 782
  · exact chk_sound _ C24 752 46487 C24_ok pc_752
      (hp_range 752 C24 (by norm_num) (by rw [C24_length]; norm_num))
      n (by omega) (by rw [C24_length]; omega)
  by_cases hc25 : n < 812
  · exact chk_sound _ C25 782 49968 C25_ok pc_782
      (hp_range 782 C25 (by norm_num) (by rw [C25_length]; norm_num))
      n (by omega) (by rw [C25_length]; omega)
  by_cases hc26 : n < 842
  · exact chk_sound _ C26 812 53514 C26_ok pc_812
      (hp_range 812 C26 (by norm_num) (by rw [C26_length]; norm_num))
      n (by omega) (by rw [C26_length]; omega)
  by_cases hc27 : n < 872
  · exact chk_sound _ C27 842 57225 C27_ok pc_842
      (hp_range 842 C27 (by norm_num) (by rw [C27_length]; norm_num))
      n (by omega) (by rw [C27_length]; omega)
  by_cases hc28 : n < 902
  · exact chk_sound _ C28 872 61008 C28_ok pc_872
      (hp_range 872 C28 (by norm_num) (by rw [C28_length]; norm_num))
      n (by omega) (by rw [C28_length]; omega)
  by_cases hc29 : n < 932
  · exact chk_sound _ C29 902 64950 C29_ok pc_902
      (hp_range 902 C29 (by norm_num) (by rw [C29_length]; norm_num))
      n (by omega) (by rw [C29_length]; omega)
  by_cases hc30 : n < 962
  · exact chk_sound _ C30 932 68991 C30_ok pc_932
      (hp_range 932 C30 (by norm_num) (by rw [C30_length]; norm_num))
      n (by omega) (by rw [C30_length]; omega)
  by_cases hc31 : n < 992
  · exact chk_sound _ C31 962 73146 C31_ok pc_962
      (hp_range 962 C31 (by norm_num) (by rw [C31_length]; norm_num))
      n (by omega) (by rw [C31_length]; omega)
  exact chk_sound _ C32 992 77354 C32_ok pc_992
      (hp_range 992 C32 (by norm_num) (by rw [C32_length]))
      n (by omega) (by rw [C32_length]; omega)

/-! ### Main theorems -/

/-- Integer-power form of Sun's Conjecture 2.14(ii). -/
theorem sun_sq_power (n : ℕ) (hn : 3 ≤ n) :
    Nat.primeCounting ((n + 1) ^ 2) ^ n < Nat.primeCounting (n ^ 2) ^ (n + 1) := by
  by_cases h : n < 1000
  · exact finite_case n hn h
  · exact large_case n (by omega)

/-- Sun's Conjecture 2.14(ii): π(n²)^(1/n) is strictly decreasing for n ≥ 3. -/
theorem sun_sq_roots (n : ℕ) (hn : 3 ≤ n) :
    (Nat.primeCounting ((n + 1) ^ 2) : ℝ) ^ (1 / ((n : ℝ) + 1)) <
      (Nat.primeCounting (n ^ 2) : ℝ) ^ (1 / (n : ℝ)) := by
  have hA : 0 < (Nat.primeCounting (n ^ 2) : ℝ) := by
    exact_mod_cast pc_pos _ (by nlinarith)
  have hB : 0 < (Nat.primeCounting ((n + 1) ^ 2) : ℝ) := by
    exact_mod_cast pc_pos _ (by nlinarith)
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpow : (Nat.primeCounting ((n + 1) ^ 2) : ℝ) ^ n <
      (Nat.primeCounting (n ^ 2) : ℝ) ^ (n + 1) := by
    exact_mod_cast sun_sq_power n hn
  have hlog := Real.log_lt_log (pow_pos hB n) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hB _) (Real.rpow_pos_of_pos hA _)).1
  rw [Real.log_rpow hB, Real.log_rpow hA]
  simp only [one_div_mul_eq_div]
  apply (div_lt_div_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 1) hnr).2
  nlinarith

#print axioms sun_sq_power
#print axioms sun_sq_roots

end SunSquares
