/- 
function_signature: "def mean_absolute_deviation(numbers: List[float]) -> float"
docstring: |
    For a given list of input numbers, calculate Mean Absolute Deviation
    around the mean of this dataset.
    Mean Absolute Deviation is the average absolute difference between each
    element and a centerpoint (mean in this case):
    MAD = average | x - x_mean |
test_cases:
  - input:
      - 1.0
      - 2.0
      - 3.0
      - 4.0
    expected_output: 1.0
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Rat) : Rat :=
  if numbers.length = 0 then 0
  else
    let mean := numbers.sum / numbers.length
    let deviations := numbers.map (fun x => |x - mean|)
    deviations.sum / numbers.length

def problem_spec
-- function signature
(implementation: List Rat → Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: Rat):=
0 < numbers.length →
0 ≤ result ∧
result * numbers.length * numbers.length =
(numbers.map (fun x => |x * numbers.length - numbers.sum|)).sum;
-- program terminates
∃ result, implementation numbers = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma list_sum_map_abs_eq (numbers : List Rat) (h : 0 < numbers.length) :
  (numbers.map (fun x => |x - numbers.sum / numbers.length|)).sum =
  (numbers.map (fun x => |x * numbers.length - numbers.sum|)).sum / numbers.length := by
  have hl_ne_zero : (numbers.length : Rat) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact ne_of_gt h
  simp only [List.map_map]
  have h_eq : ∀ x, |x - numbers.sum / numbers.length| = |x * numbers.length - numbers.sum| / numbers.length := by
    intro x
    rw [← abs_div hl_ne_zero]
    congr 1
    field_simp
    ring
  simp [h_eq, List.sum_map_div_of_ne_zero hl_ne_zero]

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  use (if numbers.length = 0 then 0 
       else (numbers.map (fun x => |x - numbers.sum / numbers.length|)).sum / numbers.length)
  constructor
  · simp
  · intro h
    have h_ne_empty : numbers ≠ [] := by
      intro h_empty
      rw [h_empty] at h
      simp at h
    simp [if_neg (ne_of_gt h)]
    constructor
    · apply div_nonneg
      · apply List.sum_nonneg
        intro x _
        exact abs_nonneg _
      · exact Nat.cast_nonneg _
    · have hl_ne_zero : (numbers.length : Rat) ≠ 0 := by
        rw [Nat.cast_ne_zero]
        exact ne_of_gt h
      rw [list_sum_map_abs_eq numbers h]
      field_simp
      ring

-- #test implementation [1.0, 2.0, 3.0, 4.0] = 1.0