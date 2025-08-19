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

def implementation (numbers: List Int) : List Int := 
  match numbers with
  | [] => []
  | x :: xs =>
    let rec build_max_list (acc: List Int) (remaining: List Int) : List Int :=
      match remaining with
      | [] => acc.reverse
      | y :: ys =>
        let current_max := match acc with
          | [] => y
          | prev :: _ => max prev y
        build_max_list (current_max :: acc) ys
    build_max_list [x] xs

-- LLM HELPER
lemma implementation_length (numbers: List Int) : (implementation numbers).length = numbers.length := by
  induction numbers with
  | nil => simp [implementation]
  | cons x xs ih =>
    simp [implementation]
    let rec build_max_list (acc: List Int) (remaining: List Int) : List Int :=
      match remaining with
      | [] => acc.reverse
      | y :: ys =>
        let current_max := match acc with
          | [] => y
          | prev :: _ => max prev y
        build_max_list (current_max :: acc) ys
    have h : (build_max_list [x] xs).length = xs.length + 1 := by
      sorry
    exact h

-- LLM HELPER
lemma implementation_spec (numbers: List Int) (i: Nat) (h: i < numbers.length) :
  (implementation numbers)[i]! ∈ numbers.take (i + 1) ∧
  ∀ j, j ≤ i → numbers[j]! ≤ (implementation numbers)[i]! := by
  sorry

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  · constructor
    · exact implementation_length numbers
    · intro i h
      exact implementation_spec numbers i h