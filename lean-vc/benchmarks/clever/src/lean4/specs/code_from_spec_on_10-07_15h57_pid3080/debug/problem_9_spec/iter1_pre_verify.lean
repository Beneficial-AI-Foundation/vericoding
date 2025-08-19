import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
result.length = numbers.length ∧
∀ i, i < numbers.length →
(result[i]! ∈ numbers.take (i + 1) ∧
∀ j, j ≤ i → numbers[j]! ≤ result[i]!);
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def max_so_far (numbers: List Int) : List Int :=
match numbers with
| [] => []
| x :: xs => 
  let rest := max_so_far xs
  match rest with
  | [] => [x]
  | y :: ys => (max x y) :: rest

def implementation (numbers: List Int) : List Int := max_so_far numbers

-- LLM HELPER
lemma max_so_far_length (numbers: List Int) : (max_so_far numbers).length = numbers.length := by
  induction numbers with
  | nil => simp [max_so_far]
  | cons x xs ih =>
    simp [max_so_far]
    cases h : max_so_far xs with
    | nil => 
      simp [max_so_far] at ih
      simp [ih]
    | cons y ys =>
      simp
      exact ih

-- LLM HELPER
lemma max_so_far_spec (numbers: List Int) (i: Nat) (h: i < numbers.length) :
  (max_so_far numbers)[i]! ∈ numbers.take (i + 1) ∧
  ∀ j, j ≤ i → numbers[j]! ≤ (max_so_far numbers)[i]! := by
  sorry

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec, implementation]
  use max_so_far numbers
  constructor
  · rfl
  · constructor
    · exact max_so_far_length numbers
    · intro i h
      exact max_so_far_spec numbers i h