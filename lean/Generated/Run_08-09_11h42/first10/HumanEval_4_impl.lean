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
  if numbers.isEmpty then 0
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
lemma list_sum_div_length_eq (numbers: List Rat) (h: 0 < numbers.length) :
  numbers.sum / numbers.length * numbers.length = numbers.sum := by
  have h_ne_zero : (numbers.length : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt h)
  rw [div_mul_cancel _ h_ne_zero]

-- LLM HELPER
lemma abs_sub_mean_eq (x : Rat) (numbers : List Rat) (h: 0 < numbers.length) :
  |x - numbers.sum / numbers.length| = |x * numbers.length - numbers.sum| / numbers.length := by
  have h_ne_zero : (numbers.length : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt h)
  rw [← abs_div]
  congr 1
  field_simp [h_ne_zero]
  ring

-- LLM HELPER  
lemma List.sum_map_div_eq (l : List Rat) (f : Rat → Rat) :
  (l.map (fun x => f x / l.length)).sum = (l.map f).sum / l.length := by
  rw [← List.sum_div]
  congr 1
  rw [List.map_map]
  rfl

-- LLM HELPER
lemma map_abs_sum_eq (numbers : List Rat) (h: 0 < numbers.length) :
  (numbers.map (fun x => |x - numbers.sum / numbers.length|)).sum = 
  (numbers.map (fun x => |x * numbers.length - numbers.sum|)).sum / numbers.length := by
  rw [← List.sum_map_div_eq]
  congr 1
  ext x
  exact abs_sub_mean_eq x numbers h

-- LLM HELPER
lemma List.ne_nil_of_not_isEmpty {α : Type*} (l : List α) (h : ¬l.isEmpty) : l ≠ [] := by
  exact List.ne_nil_of_length_pos (List.length_pos_of_ne_nil (fun h_eq => h (h_eq ▸ rfl)))

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  unfold implementation
  by_cases h : numbers.isEmpty
  · simp [h]
    use 0
    simp [List.isEmpty_iff_eq_nil.mp h]
    intro h_pos
    simp at h_pos
  · simp [h]
    have h_pos : 0 < numbers.length := List.length_pos_of_ne_nil (List.ne_nil_of_not_isEmpty numbers h)
    let mean := numbers.sum / numbers.length
    let deviations := numbers.map (fun x => |x - mean|)
    let result := deviations.sum / numbers.length
    use result
    constructor
    · rfl
    · intro h_len
      constructor
      · apply div_nonneg
        · apply List.sum_nonneg
          intro x hx
          exact abs_nonneg _
        · exact Nat.cast_nonneg _
      · rw [map_abs_sum_eq numbers h_pos]
        ring

-- #test implementation [1.0, 2.0, 3.0, 4.0] = 1.0