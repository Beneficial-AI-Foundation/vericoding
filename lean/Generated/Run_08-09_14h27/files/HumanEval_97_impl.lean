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

-- LLM HELPER
lemma abs_mod_le_nine (x : Int) : |x % 10| ≤ 9 := by
  rw [abs_le]
  constructor
  · have h := Int.emod_nonneg x (by norm_num : (10 : Int) ≠ 0)
    linarith
  · have h := Int.emod_lt_of_pos x (by norm_num : (0 : Int) < 10)
    linarith

-- LLM HELPER
lemma mul_mod_eq (a b : Int) : (a % 10) * (b % 10) % 10 = (a * b) % 10 := by
  simp [Int.mul_emod]

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
      have h1 : |a % 10| ≤ 9 := abs_mod_le_nine a
      have h2 : |b % 10| ≤ 9 := abs_mod_le_nine b
      rw [abs_mul]
      have this : |a % 10| * |b % 10| ≤ 9 * 9 := by
        apply mul_le_mul h1 h2
        · exact abs_nonneg _
        · norm_num
      norm_num at this
      exact this
    · constructor
      · -- result % 10 = (a * b) % 10
        exact mul_mod_eq a b
      · constructor
        · -- ((b%10) ≠ 0 → (result % (b%10) = 0 ∧ (result/ (b%10)) % 100 = (a%10)))
          intro hb
          constructor
          · have : a % 10 * (b % 10) = (b % 10) * (a % 10) := Int.mul_comm _ _
            rw [this]
            exact Int.mul_emod_left _ _
          · have : a % 10 * (b % 10) = (b % 10) * (a % 10) := Int.mul_comm _ _
            rw [this]
            rw [Int.mul_ediv_cancel_left _ hb]
            simp
        · constructor
          · -- ((a%10) ≠ 0 → (result % (a%10) = 0 ∧ (result/ (a%10)) % 100 = (b%10)))
            intro ha
            constructor
            · exact Int.mul_emod_left _ _
            · rw [Int.mul_ediv_cancel_left _ ha]
              simp
          · -- ((a%10 = 0) ∨ (b%10 = 0) → result = 0)
            intro h
            cases h with
            | inl ha => simp [ha]
            | inr hb => simp [hb]

-- #test implementation 148 412 = 16
-- #test implementation 19 28 = 72
-- #test implementation 2020 1851 = 0
-- #test implementation 14 -15 = 20