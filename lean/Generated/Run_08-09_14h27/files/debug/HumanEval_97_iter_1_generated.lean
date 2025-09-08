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
  simp only [exists_prop]
  constructor
  · rfl
  · simp only [abs_mul]
    constructor
    · -- |result| ≤ 81
      have h1 : |a % 10| ≤ 9 := by
        have := Int.mod_two_eq_zero_or_one (a / 10)
        simp only [abs_le]
        constructor
        · linarith [Int.mod_nonneg a (by norm_num : (10 : Int) ≠ 0)]
        · exact Int.mod_lt_of_pos a (by norm_num)
      have h2 : |b % 10| ≤ 9 := by
        simp only [abs_le]
        constructor
        · linarith [Int.mod_nonneg b (by norm_num : (10 : Int) ≠ 0)]
        · exact Int.mod_lt_of_pos b (by norm_num)
      linarith [abs_mul (a % 10) (b % 10), h1, h2]
    · constructor
      · -- result % 10 = (a * b) % 10
        simp only [Int.mul_mod]
      · constructor
        · -- ((b%10) ≠ 0 → (result % (b%10) = 0 ∧ (result/ (b%10)) % 100 = (a%10)))
          intro hb
          constructor
          · simp only [Int.mul_mod]
            rw [Int.mod_mul_left_mod]
          · simp only [Int.mul_div_cancel_of_imp_ne]
            have : (a % 10) * (b % 10) / (b % 10) = a % 10 := by
              rw [Int.mul_div_cancel']
              exact dvd_mul_left (b % 10) (a % 10)
            rw [this]
            exact Int.mod_lt_of_pos (a % 10) (by norm_num)
        · -- ((a%10) ≠ 0 → (result % (a%10) = 0 ∧ (result/ (a%10)) % 100 = (b%10))) ∧ ((a%10 = 0) ∨ (b%10 = 0) → result = 0)
          constructor
          · intro ha
            constructor
            · rw [Int.mul_mod, Int.mod_mul_right_mod]
            · have : (a % 10) * (b % 10) / (a % 10) = b % 10 := by
                rw [Int.mul_comm, Int.mul_div_cancel']
                exact dvd_mul_left (a % 10) (b % 10)
              rw [this]
              exact Int.mod_lt_of_pos (b % 10) (by norm_num)
          · intro h
            cases h with
            | inl ha => simp [ha]
            | inr hb => simp [hb]

-- #test implementation 148 412 = 16
-- #test implementation 19 28 = 72
-- #test implementation 2020 1851 = 0
-- #test implementation 14 -15 = 20