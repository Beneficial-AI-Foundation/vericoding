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
      by_contra! h_contra
      -- h_contra : |numbers[i]! - numbers[j]!| < threshold
      -- Now show the implementation should be true, contradicting h
      have : (numbers.any fun x ↦ numbers.any fun y ↦ decide (x ≠ y ∧ |x - y| < threshold)) = true := by
        rw [List.any_eq_true]
        use numbers[i]!
        constructor
        · sorry -- numbers[i]! ∈ numbers when i < numbers.length
        · rw [List.any_eq_true]
          use numbers[j]!
          constructor
          · sorry -- numbers[j]! ∈ numbers when j < numbers.length
          · simp
            constructor
            · sorry -- ¬numbers[i]?.getD default = numbers[j]?.getD default
            · convert h_contra using 1 <;> simp [hi, hj]
      exact h this

-- #test implementation ([1, 2, 3]: List Rat) 0.5 = false
-- #test implementation ([1, 2.8, 3, 4, 5, 2]: List Rat) 0.3 = true