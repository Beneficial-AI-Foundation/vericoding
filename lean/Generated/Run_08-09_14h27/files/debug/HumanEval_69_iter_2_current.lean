/- 
function_signature: "def search(numbers: List[int]) -> int"
docstring: |
    You are given a non-empty list of positive integers. Return the greatest integer that is greater than
    zero, and has a frequency greater than or equal to the value of the integer itself.
    The frequency of an integer is the number of times it appears in the list.
    If no such a value exist, return -1.
test_cases:
  - input: [4, 1, 2, 2, 3, 1]
    expected_output: 2
  - input: [1, 2, 2, 3, 3, 3, 4, 4, 4]
    expected_output: 3
  - input: [5, 5, 4, 4, 4]
    expected_output: -1
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def satisfies_condition (numbers: List Int) (x: Int) : Bool :=
  x > 0 && (numbers.count x).toInt ≥ x

-- LLM HELPER
noncomputable def get_valid_numbers (numbers: List Int) : List Int :=
  (numbers.toFinset.toList).filter (satisfies_condition numbers)

noncomputable def implementation (numbers: List Int) : (Int) :=
  let valid := get_valid_numbers numbers
  if valid.isEmpty then -1
  else valid.maximum.getD (-1)

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: Int) :=
0 < numbers.length ∧ numbers.all (fun n => 0 < n) →
(result ≠ -1 ↔ ∃ i : Nat, i < numbers.length ∧
  numbers[i]! = result ∧ numbers[i]! > 0 ∧
  numbers[i]! ≤ (numbers.filter (fun x => x = numbers[i]!)).length ∧
  (¬∃ j : Nat, j < numbers.length ∧
  numbers[i]! < numbers[j]! ∧ numbers[j]! ≤ numbers.count numbers[j]!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma count_filter_eq (numbers: List Int) (x: Int) :
  (numbers.filter (fun y => decide (y = x))).length = (numbers.filter (fun x_1 => x_1 == x)).length := by
  simp [List.filter_congr_decidable]

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  · intro ⟨hlen, hpos⟩
    constructor
    · intro h
      simp [implementation] at h
      by_cases hempty : (get_valid_numbers numbers).isEmpty
      · simp [hempty] at h
        exfalso
        exact h
      · simp [hempty] at h
        have hmax_mem : (get_valid_numbers numbers).maximum.getD (-1) ∈ get_valid_numbers numbers := by
          apply List.maximum_getD_mem
          rw [← List.isEmpty_iff_eq_nil]
          exact hempty
        simp [get_valid_numbers, satisfies_condition] at hmax_mem
        use List.indexOf (get_valid_numbers numbers).maximum.getD (-1) numbers
        sorry
    · intro ⟨i, hi, heq, hpos_i, hcount_i, hmax_i⟩
      simp [implementation]
      sorry

-- #test implementation [4, 1, 2, 2, 3, 1] = 2
-- #test implementation [1, 2, 2, 3, 3, 4, 4, 4] = 3
-- #test implementation [5, 5, 4, 4, 4] = -1