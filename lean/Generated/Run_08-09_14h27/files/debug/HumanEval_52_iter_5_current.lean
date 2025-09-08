/- 
function_signature: "def below_threshold(numbers: List[Int], threshold: Int) -> bool"
docstring: Return True if all numbers in the list l are below threshold t, and False otherwise.
test_cases:
  - input: [[1, 2, 4, 10], 100]
    expected_output: True
  - input: [[1, 20, 4, 10], 5]
    expected_output: False
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Int) (threshold: Int) : Bool :=
  numbers.all (fun x => x < threshold)

def problem_spec
-- function signature
(impl: List Int → Int → Bool)
-- inputs
(numbers: List Int)
(threshold: Int) :=
-- spec
let numbers_below_threshold :=
  ∀ i, i < numbers.length → numbers[i]! < threshold;
let spec (res: Bool) :=
(numbers.length = 0 → res) ∧
(res ↔ numbers_below_threshold)
-- program terminates
∃ result, impl numbers threshold = result ∧
-- return value satisfies spec
spec result
-- if result then spec else ¬spec

-- LLM HELPER
lemma list_all_iff_forall_get (numbers : List Int) (threshold : Int) :
  numbers.all (fun x => x < threshold) = true ↔ 
  ∀ i, i < numbers.length → numbers[i]! < threshold := by
  constructor
  · intro h i hi
    have mem : numbers[i]! ∈ numbers := List.getElem!_mem numbers i
    rw [List.all_eq_true] at h
    exact h (numbers[i]!) mem
  · intro h
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_get.mp hx
    exact h i (by simpa using hi)

theorem correctness
(numbers: List Int)
(threshold: Int)
: problem_spec implementation numbers threshold  := by
  unfold problem_spec implementation
  use numbers.all (fun x => x < threshold)
  constructor
  · rfl
  · constructor
    · intro h
      simp [List.length_eq_zero_iff] at h
      rw [h]
      simp [List.all]
    · rw [list_all_iff_forall_get]

-- #test implementation ([1, 2, 4, 10]: List Int) 100 = true
-- #test implementation ([1, 20, 4, 10]: List Int) 5 = false