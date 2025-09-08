import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Int) : List Int :=
  numbers.map (· + 1)

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
  (result.length = numbers.length) ∧
  ∀ i, i < numbers.length →
  result[i]! = numbers[i]! + 1
-- -- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma list_map_length (numbers : List Int) : (numbers.map (· + 1)).length = numbers.length := by
  simp [List.length_map]

-- LLM HELPER
lemma list_map_getElem (numbers : List Int) (i : Nat) (h : i < numbers.length) :
  (numbers.map (· + 1))[i]! = numbers[i]! + 1 := by
  simp [List.getElem!_map_apply, List.length_map]

theorem correctness
(numbers : List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  use numbers.map (· + 1)
  constructor
  · rfl
  · constructor
    · exact list_map_length numbers
    · intro i h
      exact list_map_getElem numbers i h