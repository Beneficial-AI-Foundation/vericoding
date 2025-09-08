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
lemma abs_sub_div_eq (x sum len : Rat) (hlen : len ≠ 0) :
  |x - sum / len| = |x * len - sum| / len := by
  rw [← abs_div]
  congr 1
  field_simp
  ring

-- LLM HELPER
lemma sum_map_div_eq (l : List Rat) (f : Rat → Rat) (c : Rat) (hc : c ≠ 0) :
  (l.map (fun x => f x / c)).sum = (l.map f).sum / c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [List.sum_cons, ih]
    ring

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
    simp [if_neg (List.length_ne_zero.mpr h_ne_empty)]
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
        exact abs_sub_div_eq x numbers.sum numbers.length hl_ne_zero
      simp only [List.map_map]
      have : (numbers.map (fun x => |x - numbers.sum / numbers.length|)).sum = 
             (numbers.map (fun x => |x * numbers.length - numbers.sum| / numbers.length)).sum := by
        congr 1
        ext x
        exact h_transform x
      rw [this]
      rw [sum_map_div_eq numbers (fun x => |x * numbers.length - numbers.sum|) numbers.length hl_ne_zero]
      ring

-- #test implementation [1.0, 2.0, 3.0, 4.0] = 1.0