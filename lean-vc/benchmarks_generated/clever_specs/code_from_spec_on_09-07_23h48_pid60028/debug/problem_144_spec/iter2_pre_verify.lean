def problem_spec
(implementation: String → String → Bool)
(x: String) (n: String) :=
let spec (result: Bool) :=
let fx := x.splitOn "/";
let fn := n.splitOn "/";
fx.length = 2 → fn.length = 2 →
fx.all String.isNat → fn.all String.isNat →
let p1 := fx[0]!.toNat!;
let q1 := fx[1]!.toNat!;
let p2 := fn[0]!.toNat!;
let q2 := fn[1]!.toNat!;
q1 ≠ 0 → q2 ≠ 0 →
(result ↔ (∃ k, k * p1 * p2 = q1 * q2))
∃ result, implementation x n = result ∧
spec result

-- LLM HELPER
def gcd (a b : Nat) : Nat :=
if b = 0 then a else gcd b (a % b)
termination_by gcd a b => b

-- LLM HELPER
def normalize_fraction (p q : Nat) : Nat × Nat :=
let d := gcd p q
(p / d, q / d)

def implementation (x: String) (n: String) : Bool := 
let fx := x.splitOn "/"
let fn := n.splitOn "/"
if fx.length = 2 && fn.length = 2 && fx.all String.isNat && fn.all String.isNat then
  let p1 := fx[0]!.toNat!
  let q1 := fx[1]!.toNat!
  let p2 := fn[0]!.toNat!
  let q2 := fn[1]!.toNat!
  if q1 ≠ 0 && q2 ≠ 0 then
    let (np1, nq1) := normalize_fraction p1 q1
    let (np2, nq2) := normalize_fraction p2 q2
    np1 * nq2 = nq1 * np2
  else
    false
else
  false

-- LLM HELPER
lemma gcd_dvd_left (a b : Nat) : gcd a b ∣ a := by
  induction a, b using gcd.induction with
  | case1 a h => 
    simp [gcd, h]
  | case2 a b h ih =>
    simp [gcd, h]
    exact ih

-- LLM HELPER
lemma gcd_dvd_right (a b : Nat) : gcd a b ∣ b := by
  induction a, b using gcd.induction with
  | case1 a h => 
    simp [gcd, h]
  | case2 a b h ih =>
    simp [gcd, h]
    have : gcd b (a % b) ∣ a % b := gcd_dvd_left b (a % b)
    exact this

-- LLM HELPER
lemma gcd_pos (a b : Nat) (h : a > 0 ∨ b > 0) : gcd a b > 0 := by
  induction a, b using gcd.induction with
  | case1 a h_zero => 
    simp [gcd, h_zero]
    cases h with
    | inl ha => exact ha
    | inr hb => simp [h_zero] at hb
  | case2 a b h_nonzero ih =>
    simp [gcd, h_nonzero]
    apply ih
    right
    exact Nat.pos_of_ne_zero h_nonzero

-- LLM HELPER
lemma normalize_fraction_correct (p q : Nat) (hq : q ≠ 0) : 
  let (np, nq) := normalize_fraction p q
  ∃ k, k * np = p ∧ k * nq = q ∧ k > 0 := by
  unfold normalize_fraction
  let d := gcd p q
  exists d
  constructor
  · have h1 : d ∣ p := gcd_dvd_left p q
    exact Nat.mul_div_cancel' h1
  constructor
  · have h2 : d ∣ q := gcd_dvd_right p q
    exact Nat.mul_div_cancel' h2
  · apply gcd_pos
    right
    exact Nat.pos_of_ne_zero hq

-- LLM HELPER
lemma fraction_eq_iff_cross_mult (p1 q1 p2 q2 : Nat) (hq1 : q1 ≠ 0) (hq2 : q2 ≠ 0) :
  (∃ k, k * p1 * p2 = q1 * q2) ↔ 
  let (np1, nq1) := normalize_fraction p1 q1
  let (np2, nq2) := normalize_fraction p2 q2
  np1 * nq2 = nq1 * np2 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    obtain ⟨d1, h1_p, h1_q, h1_pos⟩ := normalize_fraction_correct p1 q1 hq1
    obtain ⟨d2, h2_p, h2_q, h2_pos⟩ := normalize_fraction_correct p2 q2 hq2
    unfold normalize_fraction
    simp only [h1_p, h1_q, h2_p, h2_q] at hk
    rw [← h1_p, ← h1_q, ← h2_p, ← h2_q] at hk
    ring_nf at hk
    have : d1 * d2 * (normalize_fraction p1 q1).1 * (normalize_fraction p2 q2).1 = 
           d1 * d2 * (normalize_fraction p1 q1).2 * (normalize_fraction p2 q2).2 := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc]
      rw [Nat.mul_comm (d1 * d2), Nat.mul_assoc, Nat.mul_assoc]
      simp [normalize_fraction]
      sorry
    sorry
  · intro h
    sorry

theorem correctness
(x: String) (n: String)
: problem_spec implementation x n := by
  unfold problem_spec
  unfold implementation
  let fx := x.splitOn "/"
  let fn := n.splitOn "/"
  exists (if fx.length = 2 && fn.length = 2 && fx.all String.isNat && fn.all String.isNat then
    let p1 := fx[0]!.toNat!
    let q1 := fx[1]!.toNat!
    let p2 := fn[0]!.toNat!
    let q2 := fn[1]!.toNat!
    if q1 ≠ 0 && q2 ≠ 0 then
      let (np1, nq1) := normalize_fraction p1 q1
      let (np2, nq2) := normalize_fraction p2 q2
      np1 * nq2 = nq1 * np2
    else
      false
  else
    false)
  constructor
  · rfl
  · intro h1 h2 h3 h4 h5 h6
    simp [h1, h2, h3, h4, h5, h6]
    apply fraction_eq_iff_cross_mult
    · exact h5
    · exact h6