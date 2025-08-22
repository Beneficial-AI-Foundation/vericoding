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

def implementation (numbers: List Int) : List Int :=
  match numbers with
  | [] => []
  | h :: t => 
    let rest := implementation t
    h :: List.map (max h) rest

-- LLM HELPER
lemma implementation_length (numbers: List Int) : (implementation numbers).length = numbers.length := by
  induction numbers with
  | nil => simp [implementation]
  | cons h t ih =>
    simp [implementation]
    rw [List.length_cons, List.length_map]
    exact ih

-- LLM HELPER
lemma implementation_spec_helper (numbers: List Int) : 
  ∀ i, i < numbers.length →
  (implementation numbers)[i]! ∈ numbers.take (i + 1) ∧
  ∀ j, j ≤ i → numbers[j]! ≤ (implementation numbers)[i]! := by
  induction numbers with
  | nil => simp
  | cons h t ih =>
    intro i hi
    simp [implementation]
    cases i with
    | zero => 
      simp [List.getElem_cons_zero, List.take_succ_cons, List.take_zero]
      intro j hj
      simp at hj
      simp [hj, List.getElem_cons_zero]
    | succ i' =>
      simp [List.getElem_cons_succ, List.take_succ_cons]
      have hi' : i' < t.length := by simp at hi; exact hi
      have spec_t := ih i' hi'
      constructor
      · right
        rw [List.getElem_map]
        exact spec_t.1
      · intro j hj
        cases j with
        | zero => 
          simp [List.getElem_cons_zero, List.getElem_map]
          exact le_max_left h (implementation t)[i']!
        | succ j' =>
          simp [List.getElem_cons_succ, List.getElem_map]
          have hj' : j' ≤ i' := by simp at hj; exact Nat.le_of_succ_le_succ hj
          have spec_j := spec_t.2 j' hj'
          exact le_trans spec_j (le_max_right h (implementation t)[i']!)

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec, implementation]
  use implementation numbers
  constructor
  · rfl
  · constructor
    · exact implementation_length numbers
    · exact implementation_spec_helper numbers