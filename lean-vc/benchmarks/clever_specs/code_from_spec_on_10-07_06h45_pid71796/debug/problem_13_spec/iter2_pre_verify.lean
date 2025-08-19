def problem_spec
-- function signature
(implementation: Int → Int → Int)
-- inputs
(a b: Int) :=
-- spec
let spec (result: Int) :=
(result ∣ a) ∧
(result ∣ b) ∧
(∀ (d': Int),
(d' > 0) → (d' ∣ a) → (d' ∣ b) →
d' ≤ result);
-- program termination
∃ result, implementation a b = result ∧
spec result

-- LLM HELPER
def nat_gcd (a b : Nat) : Nat := 
  if b = 0 then a else nat_gcd b (a % b)
termination_by nat_gcd a b => b

-- LLM HELPER
def int_gcd (a b : Int) : Int :=
  Int.natAbs (nat_gcd (Int.natAbs a) (Int.natAbs b))

def implementation (a b: Int) : Int := int_gcd a b

-- LLM HELPER
lemma nat_gcd_dvd_left (a b : Nat) : (nat_gcd a b : Int) ∣ (a : Int) := by
  cases' Nat.eq_zero_or_pos b with h h
  · simp [nat_gcd, h]
  · rw [Nat.gcd_rec]
    exact Nat.gcd_dvd_left a b

-- LLM HELPER
lemma nat_gcd_dvd_right (a b : Nat) : (nat_gcd a b : Int) ∣ (b : Int) := by
  cases' Nat.eq_zero_or_pos b with h h
  · simp [nat_gcd, h]
  · rw [Nat.gcd_rec]
    exact Nat.gcd_dvd_right a b

-- LLM HELPER
lemma nat_gcd_greatest (a b : Nat) (d : Int) : d > 0 → d ∣ (a : Int) → d ∣ (b : Int) → d ≤ (nat_gcd a b : Int) := by
  intro hd_pos hd_a hd_b
  have h_pos : 0 < Int.natAbs d := by
    rw [Int.natAbs_pos]
    exact ne_of_gt hd_pos
  have h_dvd_a : Int.natAbs d ∣ a := by
    rw [Int.natAbs_dvd_iff_dvd]
    exact hd_a
  have h_dvd_b : Int.natAbs d ∣ b := by
    rw [Int.natAbs_dvd_iff_dvd]
    exact hd_b
  have h_le : Int.natAbs d ≤ nat_gcd a b := Nat.dvd_gcd_iff.mp ⟨h_dvd_a, h_dvd_b⟩
  rw [← Int.natAbs_of_nonneg (le_of_lt hd_pos)]
  exact Int.coe_nat_le_coe_nat_iff.mpr h_le

-- LLM HELPER
lemma int_gcd_dvd_left (a b : Int) : int_gcd a b ∣ a := by
  unfold int_gcd
  have h1 : (nat_gcd (Int.natAbs a) (Int.natAbs b) : Int) ∣ (Int.natAbs a : Int) := nat_gcd_dvd_left (Int.natAbs a) (Int.natAbs b)
  have h2 : (Int.natAbs a : Int) ∣ a := Int.natAbs_dvd
  exact dvd_trans h1 h2

-- LLM HELPER
lemma int_gcd_dvd_right (a b : Int) : int_gcd a b ∣ b := by
  unfold int_gcd
  have h1 : (nat_gcd (Int.natAbs a) (Int.natAbs b) : Int) ∣ (Int.natAbs b : Int) := nat_gcd_dvd_right (Int.natAbs a) (Int.natAbs b)
  have h2 : (Int.natAbs b : Int) ∣ b := Int.natAbs_dvd
  exact dvd_trans h1 h2

-- LLM HELPER
lemma int_gcd_greatest (a b : Int) (d : Int) : d > 0 → d ∣ a → d ∣ b → d ≤ int_gcd a b := by
  intro hd_pos hd_a hd_b
  unfold int_gcd
  have h1 : d ∣ (Int.natAbs a : Int) := by
    have : Int.natAbs a ∣ a := Int.natAbs_dvd
    exact dvd_trans (Int.dvd_natAbs_of_dvd hd_a) this
  have h2 : d ∣ (Int.natAbs b : Int) := by
    have : Int.natAbs b ∣ b := Int.natAbs_dvd
    exact dvd_trans (Int.dvd_natAbs_of_dvd hd_b) this
  exact nat_gcd_greatest (Int.natAbs a) (Int.natAbs b) d hd_pos h1 h2

theorem correctness
(a b: Int)
: problem_spec implementation a b
:= by
  unfold problem_spec implementation
  use int_gcd a b
  constructor
  · rfl
  · constructor
    · exact int_gcd_dvd_left a b
    · constructor
      · exact int_gcd_dvd_right a b
      · exact int_gcd_greatest a b