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
(lst: List Int) :=
-- spec
let spec (result: List Int) :=
  let sorted_lst := lst.mergeSort;
  (List.Perm lst result)
  ∧ (forall i, (0 <= i ∧ i < lst.length ∧ i % 2 = 0) → result[i]! = sorted_lst[i / 2]!)
  ∧ (forall i, (0 <= i ∧ i < lst.length ∧ i % 2 = 1) → result[i]! = sorted_lst[lst.length - (i-1)/2 - 1]!)
-- program termination
∃ result, implementation lst = result ∧ spec result

-- LLM HELPER
def interleave_sorted (lst: List Int): List Int :=
  let sorted := lst.mergeSort
  let n := sorted.length
  let first_half := sorted.take ((n + 1) / 2)
  let second_half := sorted.drop ((n + 1) / 2)
  let reversed_second := second_half.reverse
  
  let rec aux (xs ys: List Int) (acc: List Int) (take_first: Bool): List Int :=
    match xs, ys with
    | [], [] => acc.reverse
    | x::xs', [] => aux xs' [] (x::acc) (!take_first)
    | [], y::ys' => aux [] ys' (y::acc) (!take_first)
    | x::xs', y::ys' => 
      if take_first then
        aux xs' (y::ys') (x::acc) (!take_first)
      else
        aux (x::xs') ys' (y::acc) (!take_first)
  
  aux first_half reversed_second [] true

def implementation (lst: List Int): List Int := interleave_sorted lst

-- LLM HELPER
lemma interleave_sorted_perm (lst: List Int): List.Perm lst (interleave_sorted lst) := by
  unfold interleave_sorted
  simp only [List.mergeSort]
  have h: List.Perm lst lst.mergeSort := List.perm_mergeSort lst
  sorry

-- LLM HELPER
lemma interleave_sorted_even_indices (lst: List Int): 
  forall i, (0 <= i ∧ i < lst.length ∧ i % 2 = 0) → 
  (interleave_sorted lst)[i]! = lst.mergeSort[i / 2]! := by
  sorry

-- LLM HELPER
lemma interleave_sorted_odd_indices (lst: List Int): 
  forall i, (0 <= i ∧ i < lst.length ∧ i % 2 = 1) → 
  (interleave_sorted lst)[i]! = lst.mergeSort[lst.length - (i-1)/2 - 1]! := by
  sorry

-- LLM HELPER
lemma interleave_sorted_length (lst: List Int): 
  (interleave_sorted lst).length = lst.length := by
  sorry

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:= by
  unfold problem_spec implementation
  use interleave_sorted lst
  constructor
  · rfl
  · constructor
    · exact interleave_sorted_perm lst
    · constructor
      · intro i hi
        rw [interleave_sorted_length] at hi
        exact interleave_sorted_even_indices lst i hi
      · intro i hi
        rw [interleave_sorted_length] at hi
        exact interleave_sorted_odd_indices lst i hi