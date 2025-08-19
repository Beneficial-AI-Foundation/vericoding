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
def running_max_aux (acc : List Int) (remaining : List Int) : List Int :=
match remaining with
| [] => acc.reverse
| x :: xs => 
  let new_max := if acc.isEmpty then x else max acc.head! x
  running_max_aux (new_max :: acc) xs

def implementation (numbers: List Int) : List Int := 
match numbers with
| [] => []
| x :: xs => 
  let rec aux (acc : List Int) (remaining : List Int) : List Int :=
    match remaining with
    | [] => acc.reverse
    | y :: ys => 
      let current_max := if acc.isEmpty then y else max acc.head! y
      aux (current_max :: acc) ys
  aux [x] xs

-- LLM HELPER
lemma take_length_eq (l : List α) (n : Nat) : n ≤ l.length → (l.take n).length = n := by
  intro h
  exact List.length_take_of_le h

-- LLM HELPER
lemma getElem_mem_take (l : List α) (i : Nat) (h : i < l.length) : l[i]! ∈ l.take (i + 1) := by
  rw [List.getElem_eq_get]
  apply List.get_mem_take
  simp [Nat.lt_add_one]
  exact h

-- LLM HELPER  
lemma implementation_length (numbers : List Int) : (implementation numbers).length = numbers.length := by
  cases numbers with
  | nil => simp [implementation]
  | cons x xs => 
    simp [implementation]
    sorry

-- LLM HELPER
lemma implementation_spec_aux (numbers : List Int) (i : Nat) (h : i < numbers.length) :
  (implementation numbers)[i]! ∈ numbers.take (i + 1) ∧
  ∀ j, j ≤ i → numbers[j]! ≤ (implementation numbers)[i]! := by
  sorry

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use implementation numbers
  constructor
  · rfl
  · constructor
    · exact implementation_length numbers
    · intro i hi
      exact implementation_spec_aux numbers i hi