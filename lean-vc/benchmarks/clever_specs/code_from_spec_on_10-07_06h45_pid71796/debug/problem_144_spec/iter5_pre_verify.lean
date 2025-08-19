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
termination_by b
decreasing_by simp_wf; exact Nat.mod_lt _ (Nat.pos_of_ne_zero (by assumption))

-- LLM HELPER
def simplify_fraction (p q : Nat) : Nat × Nat :=
if q = 0 then (0, 1)
else
  let g := gcd p q
  (p / g, q / g)

def implementation (x: String) (n: String) : Bool :=
let fx := x.splitOn "/"
let fn := n.splitOn "/"
if fx.length = 2 && fn.length = 2 &&
   fx.all String.isNat = true && fn.all String.isNat = true then
  let p1 := fx[0]!.toNat!
  let q1 := fx[1]!.toNat!
  let p2 := fn[0]!.toNat!
  let q2 := fn[1]!.toNat!
  if q1 ≠ 0 && q2 ≠ 0 then
    let (p1_simp, q1_simp) := simplify_fraction p1 q1
    let (p2_simp, q2_simp) := simplify_fraction p2 q2
    p1_simp * q2_simp = q1_simp * p2_simp
  else
    false
else
  false

-- LLM HELPER
lemma gcd_dvd_left (a b : Nat) : gcd a b ∣ a := by
  revert b
  induction a using Nat.strong_induction with
  | ind a ih =>
    intro b
    unfold gcd
    split_ifs with h
    · simp
    · have : b % a < a := Nat.mod_lt b (Nat.pos_of_ne_zero h)
      exact ih (b % a) this b

-- LLM HELPER
lemma gcd_dvd_right (a b : Nat) : gcd a b ∣ b := by
  revert b
  induction a using Nat.strong_induction with
  | ind a ih =>
    intro b
    unfold gcd
    split_ifs with h
    · simp [h]
    · have : b % a < a := Nat.mod_lt b (Nat.pos_of_ne_zero h)
      have h1 := ih (b % a) this b
      have h2 := gcd_dvd_left (b % a) b
      rw [Nat.dvd_iff_mod_eq_zero] at h2 ⊢
      rw [← Nat.add_mul_mod_self_left b 1 a] at h2
      simp at h2
      exact h2

-- LLM HELPER
lemma simplify_fraction_correct (p q : Nat) (hq : q ≠ 0) :
  let (p', q') := simplify_fraction p q
  ∃ k, k * p' = p ∧ k * q' = q ∧ q' ≠ 0 := by
  unfold simplify_fraction
  simp [hq]
  let g := gcd p q
  use g
  constructor
  · rw [Nat.mul_div_cancel' (gcd_dvd_left p q)]
  constructor
  · rw [Nat.mul_div_cancel' (gcd_dvd_right p q)]
  · intro h
    have : g ∣ q := gcd_dvd_right p q
    rw [Nat.dvd_iff_mod_eq_zero] at this
    have : q = g * (q / g) := (Nat.mul_div_cancel' this).symm
    rw [this, h, mul_zero] at hq
    exact hq rfl

-- LLM HELPER
lemma cross_mult_iff_prop_equal (p1 q1 p2 q2 : Nat) (hq1 : q1 ≠ 0) (hq2 : q2 ≠ 0) :
  (∃ k, k * p1 * p2 = q1 * q2) ↔ 
  (let (p1', q1') := simplify_fraction p1 q1
   let (p2', q2') := simplify_fraction p2 q2
   p1' * q2' = q1' * p2') := by
  constructor
  · intro ⟨k, hk⟩
    obtain ⟨g1, hg1_p, hg1_q, hg1_ne⟩ := simplify_fraction_correct p1 q1 hq1
    obtain ⟨g2, hg2_p, hg2_q, hg2_ne⟩ := simplify_fraction_correct p2 q2 hq2
    simp [simplify_fraction]
    rw [← hg1_p, ← hg1_q, ← hg2_p, ← hg2_q] at hk
    rw [mul_assoc, mul_assoc] at hk
    rw [mul_comm (g1 * (p1 / gcd p1 q1)) (g2 * (p2 / gcd p2 q2))] at hk
    rw [← mul_assoc, ← mul_assoc] at hk
    have : g1 * g2 ≠ 0 := by
      intro h
      cases' Nat.mul_eq_zero.mp h with h h
      · rw [← hg1_q] at h
        simp at h
        exact hq1 h
      · rw [← hg2_q] at h
        simp at h
        exact hq2 h
    rw [← mul_assoc k, mul_assoc (g1 * g2)] at hk
    exact Nat.mul_left_cancel this hk
  · intro h
    obtain ⟨g1, hg1_p, hg1_q, hg1_ne⟩ := simplify_fraction_correct p1 q1 hq1
    obtain ⟨g2, hg2_p, hg2_q, hg2_ne⟩ := simplify_fraction_correct p2 q2 hq2
    use g1 * g2
    rw [← hg1_p, ← hg1_q, ← hg2_p, ← hg2_q]
    rw [mul_assoc, mul_assoc]
    rw [mul_comm (g1 * (p1 / gcd p1 q1)) (g2 * (p2 / gcd p2 q2))]
    rw [← mul_assoc, ← mul_assoc]
    rw [← mul_assoc (g1 * g2)]
    rw [mul_assoc (g1 * g2)]
    simp [simplify_fraction] at h
    exact h

theorem correctness
(x: String) (n: String)
: problem_spec implementation x n := by
  unfold problem_spec
  let fx := x.splitOn "/"
  let fn := n.splitOn "/"
  use implementation x n
  constructor
  · rfl
  · intro h1 h2 h3 h4
    let p1 := fx[0]!.toNat!
    let q1 := fx[1]!.toNat!
    let p2 := fn[0]!.toNat!
    let q2 := fn[1]!.toNat!
    intro hq1 hq2
    unfold implementation
    simp [h1, h2, h3, h4, hq1, hq2]
    exact cross_mult_iff_prop_equal p1 q1 p2 q2 hq1 hq2