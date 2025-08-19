import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Int → Int → Int)
-- inputs
(a b: Int) :=
-- spec
let spec (result : Int) :=
  |result| ≤ 81 ∧
  result % 10 = (a * b) % 10 ∧
  ((b%10) ≠ 0 → (result % (b%10) = 0 ∧ (result/ (b%10)) % 100 = (a%10))) ∧
  ((a%10) ≠ 0 → (result % (a%10) = 0 ∧ (result/ (a%10)) % 100 = (b%10))) ∧
  ((a%10 = 0) ∨ (b%10 = 0) → result = 0)
-- program termination
∃ result,
  implementation a b = result ∧
  spec result

def implementation (a b: Int) : Int := 
  if (a % 10 = 0) ∨ (b % 10 = 0) then 0 
  else (a % 10) * (b % 10)

-- LLM HELPER
lemma abs_le_of_small_product (a b : Int) : 
  |a % 10| ≤ 9 ∧ |b % 10| ≤ 9 → |(a % 10) * (b % 10)| ≤ 81 := by
  intro h
  have ha : |a % 10| ≤ 9 := h.1
  have hb : |b % 10| ≤ 9 := h.2
  rw [abs_mul]
  exact mul_le_mul' ha hb

-- LLM HELPER  
lemma mod_bounds (n : Int) : |n % 10| ≤ 9 := by
  have h1 : -9 ≤ n % 10 := by
    have : n % 10 > -10 := Int.emod_neg_lt_of_pos n (by norm_num : (0 : Int) < 10)
    linarith
  have h2 : n % 10 ≤ 9 := by
    have : n % 10 < 10 := Int.emod_lt_of_pos n (by norm_num : (0 : Int) < 10)
    linarith
  rw [abs_le]
  exact ⟨h1, h2⟩

-- LLM HELPER
lemma implementation_zero_cases (a b : Int) :
  (a % 10 = 0 ∨ b % 10 = 0) → implementation a b = 0 := by
  intro h
  unfold implementation
  simp [h]

-- LLM HELPER  
lemma implementation_nonzero_cases (a b : Int) :
  (a % 10 ≠ 0 ∧ b % 10 ≠ 0) → implementation a b = (a % 10) * (b % 10) := by
  intro h
  unfold implementation
  simp [h.1, h.2]

theorem correctness
(a b: Int)
: problem_spec implementation a b
:= by
  unfold problem_spec
  use implementation a b
  constructor
  · rfl
  · by_cases h : (a % 10 = 0 ∨ b % 10 = 0)
    · -- Case: one of a%10 or b%10 is zero
      rw [implementation_zero_cases a b h]
      simp only [abs_zero, zero_le', zero_mod, true_and]
      constructor
      · -- result % 10 = (a * b) % 10
        rw [Int.zero_mod, Int.mul_mod]
        cases' h with ha hb
        · rw [ha, zero_mul, zero_mod]
        · rw [hb, mul_zero, zero_mod]
      constructor
      · -- (b%10) ≠ 0 → ...
        intro hb_ne_zero
        cases' h with ha hb
        · simp
        · contradiction
      constructor  
      · -- (a%10) ≠ 0 → ...
        intro ha_ne_zero
        cases' h with ha hb
        · contradiction
        · simp
      · -- (a%10 = 0) ∨ (b%10 = 0) → result = 0
        intro
        rfl
    · -- Case: both a%10 and b%10 are nonzero
      push_neg at h
      rw [implementation_nonzero_cases a b h]
      constructor
      · -- |result| ≤ 81
        apply abs_le_of_small_product
        exact ⟨mod_bounds a, mod_bounds b⟩
      constructor
      · -- result % 10 = (a * b) % 10
        rw [Int.mul_mod, Int.mul_mod]
      constructor
      · -- (b%10) ≠ 0 → ...
        intro hb_ne_zero
        constructor
        · -- result % (b%10) = 0
          rw [Int.mul_mod]
          simp
        · -- (result / (b%10)) % 100 = (a%10)
          rw [Int.mul_ediv_cancel_right (a % 10) h.2]
          have : |a % 10| < 100 := by
            have : |a % 10| ≤ 9 := mod_bounds a
            linarith
          rw [Int.mod_eq_of_lt]
          · exact Int.abs_nonneg _
          · exact this
      constructor
      · -- (a%10) ≠ 0 → ...
        intro ha_ne_zero
        constructor
        · -- result % (a%10) = 0
          rw [Int.mul_comm, Int.mul_mod]
          simp
        · -- (result / (a%10)) % 100 = (b%10)
          rw [Int.mul_comm, Int.mul_ediv_cancel_right (b % 10) h.1]
          have : |b % 10| < 100 := by
            have : |b % 10| ≤ 9 := mod_bounds b
            linarith
          rw [Int.mod_eq_of_lt]
          · exact Int.abs_nonneg _
          · exact this
      · -- (a%10 = 0) ∨ (b%10 = 0) → result = 0
        intro h_contra
        exfalso
        exact h h_contra