/- 
function_signature: "def has_close_elements(numbers: List[float], threshold: float) -> bool"
docstring: Check if in given list of numbers, are any two numbers closer to each other than given threshold.
test_cases:
  - input: [[1.0, 2.0, 3.0], 0.5]
    expected_output: False
  - input: [[1.0, 2.8, 3.0, 4.0, 5.0, 2.0], 0.3]
    expected_output: True
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Rat) (threshold: Rat) : Bool :=
  -- Check if there exist indices i,j with i≠j and close values
  (List.range numbers.length).any fun i => 
    (List.range numbers.length).any fun j => 
      i ≠ j ∧ |numbers[i]! - numbers[j]!| < threshold

def problem_spec
-- function signature
(impl: List Rat → Rat → Bool)
-- inputs
(numbers: List Rat)
(threshold: Rat) :=
-- spec
let numbers_within_threshold :=
(∃ i j, i < numbers.length ∧ j < numbers.length ∧
i ≠ j ∧ |numbers[i]! - numbers[j]!| < threshold);
let spec (res: Bool) :=
numbers.length > 1 →
if res then numbers_within_threshold else ¬numbers_within_threshold;
-- program terminates
∃ result, impl numbers threshold = result ∧
-- return value satisfies spec
spec result
-- if result then spec else ¬spec

theorem correctness
(numbers: List Rat)
(threshold: Rat)
: problem_spec implementation numbers threshold  := by
  -- Start fresh with new implementation
  unfold problem_spec implementation  
  use ((List.range numbers.length).any fun i => 
        (List.range numbers.length).any fun j => 
          i ≠ j ∧ |numbers[i]! - numbers[j]!| < threshold)
  constructor
  · -- Show implementation equals the boolean we're using
    rfl
  · intro h_len
    split_ifs with h
    · -- Case: implementation returns true
      rw [List.any_eq_true] at h
      obtain ⟨i, hi_mem, hi⟩ := h
      rw [List.any_eq_true] at hi
      obtain ⟨j, hj_mem, hij⟩ := hi
      simp at hij
      -- Convert membership in range to bounds
      rw [List.mem_range] at hi_mem hj_mem
      -- Extract parts of hij
      obtain ⟨hij_ne, hij_lt⟩ := hij
      -- Provide witnesses
      use i, j
      exact ⟨hi_mem, hj_mem, hij_ne, by convert hij_lt using 1; simp [hi_mem, hj_mem]⟩
    · -- Case: implementation returns false
      push_neg
      intros i j hi hj hij_ne
      by_contra! h_contra
      -- h_contra : |numbers[i]! - numbers[j]!| < threshold
      -- Now show the implementation should be true, contradicting h
      have : ((List.range numbers.length).any fun i' => 
               (List.range numbers.length).any fun j' => 
                 i' ≠ j' ∧ |numbers[i']! - numbers[j']!| < threshold) = true := by
        rw [List.any_eq_true]
        use i
        constructor
        · exact List.mem_range.mpr hi
        · rw [List.any_eq_true]
          use j  
          constructor
          · exact List.mem_range.mpr hj
          · simp [hij_ne]
            convert h_contra using 1 <;> simp [hi, hj]
      exact h this

#eval implementation ([1, 2, 3]: List Rat) (1/2) -- Should be false
#eval implementation ([1, 28/10, 3, 4, 5, 2]: List Rat) (3/10) -- Should be true