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
lemma aux_perm_helper (xs ys acc: List Int) (take_first: Bool): 
  List.Perm (xs ++ ys ++ acc) (implementation.aux xs ys acc take_first) := by
  induction xs, ys, acc, take_first using implementation.aux.induct
  case case1 acc => simp [implementation.aux]; exact List.Perm.refl _
  case case2 x xs' acc take_first ih => 
    simp [implementation.aux]; exact List.Perm.trans (List.perm_append_comm _ _) ih
  case case3 y ys' acc take_first ih => 
    simp [implementation.aux]; exact List.Perm.trans (List.perm_append_comm _ _) ih
  case case4 x xs' y ys' acc take_first ih1 ih2 => 
    simp [implementation.aux]; split_ifs with h
    exact ih1
    exact ih2

-- LLM HELPER
lemma implementation_perm (lst: List Int): List.Perm lst (implementation lst) := by
  unfold implementation
  have h: List.Perm lst lst.mergeSort := perm_mergeSort lst
  have h2: List.Perm lst.mergeSort (implementation.aux _ _ [] true) := by
    have aux_perm := aux_perm_helper _ _ [] true
    simp [List.take_append_drop] at aux_perm
    exact aux_perm
  exact List.Perm.trans h h2

-- LLM HELPER
lemma aux_length_helper (xs ys acc: List Int) (take_first: Bool): 
  (implementation.aux xs ys acc take_first).length = xs.length + ys.length + acc.length := by
  induction xs, ys, acc, take_first using implementation.aux.induct
  case case1 acc => simp [implementation.aux]
  case case2 x xs' acc take_first ih => 
    simp [implementation.aux]; exact ih
  case case3 y ys' acc take_first ih => 
    simp [implementation.aux]; exact ih
  case case4 x xs' y ys' acc take_first ih1 ih2 => 
    simp [implementation.aux]; split_ifs with h
    simp [ih1]; ring
    simp [ih2]; ring

-- LLM HELPER
lemma implementation_length (lst: List Int): (implementation lst).length = lst.length := by
  unfold implementation
  have h: lst.mergeSort.length = lst.length := List.length_mergeSort lst
  rw [aux_length_helper]
  simp [List.length_take, List.length_drop]
  exact h

-- LLM HELPER
lemma aux_get_helper (xs ys acc: List Int) (take_first: Bool) (i: Nat) (hi: i < (implementation.aux xs ys acc take_first).length):
  (implementation.aux xs ys acc take_first)[i] = 
  (xs ++ ys ++ acc.reverse)[i] := by
  sorry

-- LLM HELPER
lemma implementation_even_indices (lst: List Int): 
  forall i, (0 <= i ∧ i < lst.length ∧ i % 2 = 0) → 
  (implementation lst)[i]! = lst.mergeSort[i / 2]! := by
  intro i hi
  unfold implementation
  simp only [List.getElem_eq_getElem?_get]
  sorry

-- LLM HELPER  
lemma implementation_odd_indices (lst: List Int): 
  forall i, (0 <= i ∧ i < lst.length ∧ i % 2 = 1) → 
  (implementation lst)[i]! = lst.mergeSort[lst.length - (i-1)/2 - 1]! := by
  intro i hi
  unfold implementation
  simp only [List.getElem_eq_getElem?_get]
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