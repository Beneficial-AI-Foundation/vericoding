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
lemma abs_div_eq (x y : Rat) (hy : y ≠ 0) : |x / y| = |x| / |y| := by
  exact abs_div x y

-- LLM HELPER
lemma abs_sub_div_eq_abs_sub_div (x sum len : Rat) (hlen : len ≠ 0) :
  |x - sum / len| = |x * len - sum| / len := by
  rw [← abs_div_eq, div_sub_div_eq_sub_div]
  simp [abs_of_pos (Rat.cast_pos.mpr (Nat.cast_pos.mp (by rwa [Nat.cast_ne_zero] at hlen)))]

-- LLM HELPER
lemma sum_map_div (l : List Rat) (f : Rat → Rat) (c : Rat) :
  (l.map (fun x => f x / c)).sum = (l.map f).sum / c := by
  rw [List.sum_map_div_left]

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  use (if numbers.length = 0 then 0 
       else (numbers.map (fun x => |x - numbers.sum / numbers.length|)).sum / numbers.length)
  constructor
  · rfl
  · intro h
    have h_ne_empty : numbers ≠ [] := by
      intro h_empty
      rw [h_empty] at h
      simp at h
    have hl_pos : (0 : Rat) < numbers.length := Nat.cast_pos.mpr h
    have hl_ne_zero : (numbers.length : Rat) ≠ 0 := ne_of_gt hl_pos
    simp [if_neg (ne_of_gt h)]
    constructor
    · -- Prove non-negativity
      apply div_nonneg
      · apply List.sum_nonneg
        intro x _
        exact abs_nonneg _
      · exact Nat.cast_nonneg _
    · -- Prove the main equality
      have h_transform : ∀ x, |x - numbers.sum / numbers.length| = |x * numbers.length - numbers.sum| / numbers.length := by
        intro x
        rw [← abs_div_eq hl_ne_zero]
        congr 1
        field_simp
        ring
      simp only [List.map_congr h_transform]
      rw [sum_map_div]
      field_simp
      ring

-- #test implementation [1.0, 2.0, 3.0, 4.0] = 1.0