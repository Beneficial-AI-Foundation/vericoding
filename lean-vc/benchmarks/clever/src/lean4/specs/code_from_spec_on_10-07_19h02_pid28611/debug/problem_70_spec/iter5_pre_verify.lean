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

def implementation (lst: List Int): List Int :=
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

-- LLM HELPER
lemma perm_mergeSort (lst: List Int): List.Perm lst lst.mergeSort := by
  exact List.perm_mergeSort lst

-- LLM HELPER  
lemma implementation_perm (lst: List Int): List.Perm lst (implementation lst) := by
  unfold implementation
  have h: List.Perm lst lst.mergeSort := perm_mergeSort lst
  have h2: List.Perm lst.mergeSort (implementation lst) := by
    unfold implementation
    rw [List.perm_ext_iff]
    intro x
    simp only [List.count_mergeSort]
    have h_take_drop: lst.mergeSort = (lst.mergeSort.take ((lst.mergeSort.length + 1) / 2)) ++ (lst.mergeSort.drop ((lst.mergeSort.length + 1) / 2)) := by
      exact List.take_append_drop ((lst.mergeSort.length + 1) / 2) lst.mergeSort
    sorry
  exact List.Perm.trans h h2

-- LLM HELPER
lemma implementation_length (lst: List Int): (implementation lst).length = lst.length := by
  unfold implementation
  have h: lst.mergeSort.length = lst.length := List.length_mergeSort lst
  rw [← h]
  sorry

-- LLM HELPER
lemma implementation_even_indices (lst: List Int): 
  forall i, (0 <= i ∧ i < lst.length ∧ i % 2 = 0) → 
  (implementation lst)[i]! = lst.mergeSort[i / 2]! := by
  intro i hi
  unfold implementation
  sorry

-- LLM HELPER  
lemma implementation_odd_indices (lst: List Int): 
  forall i, (0 <= i ∧ i < lst.length ∧ i % 2 = 1) → 
  (implementation lst)[i]! = lst.mergeSort[lst.length - (i-1)/2 - 1]! := by
  intro i hi
  unfold implementation
  sorry

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:= by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · constructor
    · exact implementation_perm lst
    · constructor
      · exact implementation_even_indices lst
      · exact implementation_odd_indices lst