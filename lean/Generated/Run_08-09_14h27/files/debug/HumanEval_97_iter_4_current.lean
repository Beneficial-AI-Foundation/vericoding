/- 
function_signature: "def multiply(a : Int, b : Int) -> Int"
docstring: |
    Complete the function that takes two integers and returns
    the product of their unit digits.
    Assume the input is always valid.
    -- Note(George): I'm finding it hard to not leak the implementation here, so I opted to make the spec more convoluted.
test_cases:
  - input: 148, 412
    expected_output: 16
  - input: 19, 28
    expected_output: 72
  - input: 2020, 1851
    expected_output: 0
  - input: 14, -15
    expected_output: 20
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (a b: Int) : Int :=
  (a % 10) * (b % 10)

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

theorem correctness
(a b: Int)
: problem_spec implementation a b
:= by
  unfold problem_spec implementation
  use (a % 10) * (b % 10)
  constructor
  · rfl
  · constructor
    · -- |result| ≤ 81
      have h1 : |a % 10| ≤ 9 := by
        rw [abs_le]
        constructor
        · have := Int.emod_nonneg a (by norm_num : (10 : Int) ≠ 0)
          linarith
        · have := Int.emod_lt_of_pos a (by norm_num : (0 : Int) < 10)
          linarith
      have h2 : |b % 10| ≤ 9 := by
        rw [abs_le]
        constructor
        · have := Int.emod_nonneg b (by norm_num : (10 : Int) ≠ 0)
          linarith
        · have := Int.emod_lt_of_pos b (by norm_num : (0 : Int) < 10)
          linarith
      rw [abs_mul]
      have : |a % 10| * |b % 10| ≤ 9 * 9 := by
        apply mul_le_mul
        · exact h1
        · exact h2
        · abs_nonneg
        · linarith
      norm_num at this
      exact this
    · constructor
      · -- result % 10 = (a * b) % 10
        simp [Int.mul_emod]
      · constructor
        · -- ((b%10) ≠ 0 → (result % (b%10) = 0 ∧ (result/ (b%10)) % 100 = (a%10)))
          intro hb
          constructor
          · simp [Int.mul_emod_right_of_pos]
            have : a % 10 * (b % 10) = (b % 10) * (a % 10) := Int.mul_comm _ _
            rw [this]
            exact Int.mul_emod_left _ _
          · simp [Int.mul_ediv_cancel']
            rw [Int.mul_comm]
            exact Int.mul_ediv_cancel_of_emod_eq_zero (Int.dvd_refl _)
        · constructor
          · -- ((a%10) ≠ 0 → (result % (a%10) = 0 ∧ (result/ (a%10)) % 100 = (b%10)))
            intro ha
            constructor
            · exact Int.mul_emod_left _ _
            · simp [Int.mul_ediv_cancel']
              exact Int.mul_ediv_cancel_of_emod_eq_zero (Int.dvd_refl _)
          · -- ((a%10 = 0) ∨ (b%10 = 0) → result = 0)
            intro h
            cases h with
            | inl ha => simp [ha]
            | inr hb => simp [hb]

-- #test implementation 148 412 = 16
-- #test implementation 19 28 = 72
-- #test implementation 2020 1851 = 0
-- #test implementation 14 -15 = 20