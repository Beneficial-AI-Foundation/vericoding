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
decreasing_by simp_wf; exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹b ≠ 0›)

-- LLM HELPER
def normalize_fraction (p q : Nat) : Nat × Nat :=
let d := gcd p q
(p / d, q / d)

def implementation (x: String) (n: String) : Bool := 
let fx := x.splitOn "/"
let fn := n.splitOn "/"
if (decide (fx.length = 2) && decide (fn.length = 2) && fx.all String.isNat && fn.all String.isNat) = true then
  let p1 := fx[0]!.toNat!
  let q1 := fx[1]!.toNat!
  let p2 := fn[0]!.toNat!
  let q2 := fn[1]!.toNat!
  if (decide (q1 ≠ 0) && decide (q2 ≠ 0)) = true then
    decide (p1 * q2 = q1 * p2)
  else
    false
else
  false

-- LLM HELPER
lemma fraction_eq_iff_cross_mult (p1 q1 p2 q2 : Nat) (hq1 : q1 ≠ 0) (hq2 : q2 ≠ 0) :
  (∃ k, k * p1 * p2 = q1 * q2) ↔ (p1 * q2 = q1 * p2) := by
  constructor
  · intro ⟨k, hk⟩
    by_cases h : p1 = 0
    · subst h
      simp at hk
      simp [hk]
    · by_cases h2 : p2 = 0
      · subst h2
        simp at hk
        simp [hk]
      · have hp1_pos : p1 > 0 := Nat.pos_of_ne_zero h
        have hp2_pos : p2 > 0 := Nat.pos_of_ne_zero h2
        have hq1_pos : q1 > 0 := Nat.pos_of_ne_zero hq1
        have hq2_pos : q2 > 0 := Nat.pos_of_ne_zero hq2
        by_cases hk0 : k = 0
        · subst hk0
          simp at hk
          rw [hk]
          simp
        · have k_pos : k > 0 := Nat.pos_of_ne_zero hk0
          have : k * (p1 * p2) = q1 * q2 := by rw [← Nat.mul_assoc]; exact hk
          rw [← this]
          ring
  · intro h
    use 1
    simp [one_mul]
    exact h

theorem correctness
(x: String) (n: String)
: problem_spec implementation x n := by
  unfold problem_spec
  unfold implementation
  let fx := x.splitOn "/"
  let fn := n.splitOn "/"
  use (if (decide (fx.length = 2) && decide (fn.length = 2) && fx.all String.isNat && fn.all String.isNat) = true then
    let p1 := fx[0]!.toNat!
    let q1 := fx[1]!.toNat!
    let p2 := fn[0]!.toNat!
    let q2 := fn[1]!.toNat!
    if (decide (q1 ≠ 0) && decide (q2 ≠ 0)) = true then
      decide (p1 * q2 = q1 * p2)
    else
      false
  else
    false)
  constructor
  · rfl
  · intro h1 h2 h3 h4 h5 h6
    simp [h1, h2, h3, h4, h5, h6]
    rw [decide_eq_true_iff]
    apply fraction_eq_iff_cross_mult
    exact h5
    exact h6