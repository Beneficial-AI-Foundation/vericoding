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
def running_max (numbers: List Int) : List Int :=
match numbers with
| [] => []
| head :: tail => 
  let rest := running_max tail
  head :: rest.map (fun x => max head x)

-- LLM HELPER
def running_max_correct_implementation (numbers: List Int) : List Int :=
match numbers with
| [] => []
| head :: tail =>
  let rec aux (acc : List Int) (remaining : List Int) (current_max : Int) : List Int :=
    match remaining with
    | [] => acc.reverse
    | x :: xs => 
      let new_max := max current_max x
      aux (new_max :: acc) xs new_max
  aux [head] tail head

def implementation (numbers: List Int) : List Int := 
match numbers with
| [] => []
| head :: tail =>
  let rec aux (acc : List Int) (remaining : List Int) (current_max : Int) : List Int :=
    match remaining with
    | [] => acc.reverse
    | x :: xs => 
      let new_max := max current_max x
      aux (new_max :: acc) xs new_max
  aux [head] tail head

-- LLM HELPER
lemma aux_length (acc : List Int) (remaining : List Int) (current_max : Int) :
  let rec aux (acc : List Int) (remaining : List Int) (current_max : Int) : List Int :=
    match remaining with
    | [] => acc.reverse
    | x :: xs => 
      let new_max := max current_max x
      aux (new_max :: acc) xs new_max
  (aux acc remaining current_max).length = acc.length + remaining.length := by
  sorry

-- LLM HELPER
lemma implementation_length (numbers: List Int) : 
  (implementation numbers).length = numbers.length := by
  cases numbers with
  | nil => simp [implementation]
  | cons head tail => 
    simp [implementation]
    sorry

-- LLM HELPER
lemma implementation_element_bound (numbers: List Int) (i : Nat) (hi : i < numbers.length) :
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
  constructor
  · exact implementation_length numbers
  · exact implementation_element_bound numbers