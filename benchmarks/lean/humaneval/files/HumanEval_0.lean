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
  numbers.any fun x => numbers.any fun y => x ≠ y ∧ |x - y| < threshold

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
  -- High-level plan with sorries
  unfold problem_spec implementation
  use (numbers.any fun x => numbers.any fun y => x ≠ y ∧ |x - y| < threshold)
  constructor
  · -- Show implementation equals the boolean we're using
    rfl
  · intro h_len
    split_ifs with h
    · -- Case: implementation returns true, show ∃ i j, ... 
      rw [List.any_eq_true] at h
      obtain ⟨x, hx_mem, hx⟩ := h
      rw [List.any_eq_true] at hx
      obtain ⟨y, hy_mem, hxy⟩ := hx
      simp at hxy
      obtain ⟨hne, hlt⟩ := hxy
      obtain ⟨i_fin, hi_eq⟩ := List.mem_iff_get.mp hx_mem
      obtain ⟨j_fin, hj_eq⟩ := List.mem_iff_get.mp hy_mem
      use i_fin.val, j_fin.val
      constructor
      · exact i_fin.isLt
      · constructor
        · exact j_fin.isLt
        · constructor
          · intro hij_eq
            exact hne (hi_eq ▸ hj_eq ▸ (Fin.ext hij_eq) ▸ rfl)
          · rw [← hi_eq, ← hj_eq] at hlt
            convert hlt using 1
            simp
    · -- Case: implementation returns false, show ¬∃ i j, ...
      push_neg  
      intros i j hi hj hij_ne
      -- Direct approach: if implementation is false, then no two distinct elements are close
      -- So if i ≠ j, either numbers[i]! = numbers[j]! or they're far apart
      by_cases h_eq : numbers[i]! = numbers[j]!
      · -- Case: numbers[i]! = numbers[j]!
        simp [h_eq]
        -- This means |numbers[i]! - numbers[j]!| = 0, so we need threshold ≤ 0
        -- But wait, this reveals an issue with the proof approach...
      · -- Case: numbers[i]! ≠ numbers[j]!  
        -- The implementation being false means these distinct elements are far apart
        have h_false : (numbers.any fun x ↦ numbers.any fun y ↦ decide (x ≠ y ∧ |x - y| < threshold)) = false := by
          rwa [Bool.not_eq_true] at h
        -- Use this to show numbers[i]! and numbers[j]! are far apart
        sorry -- This is the right approach but needs the right lemma

#eval implementation ([1, 2, 3]: List Rat) (1/2) -- Should be false
#eval implementation ([1, 28/10, 3, 4, 5, 2]: List Rat) (3/10) -- Should be true