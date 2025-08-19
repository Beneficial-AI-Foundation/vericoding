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
  let sorted_lst := lst.mergeSort
  let first_half := sorted_lst.take ((sorted_lst.length + 1) / 2)
  let second_half := sorted_lst.drop ((sorted_lst.length + 1) / 2)
  let rev_second_half := second_half.reverse
  List.zipWith (fun a b => [a, b]) first_half rev_second_half |>.join

def implementation (lst: List Int): List Int := 
  let sorted_lst := lst.mergeSort
  let n := sorted_lst.length
  let first_half := sorted_lst.take ((n + 1) / 2)
  let second_half := sorted_lst.drop ((n + 1) / 2)
  let rev_second_half := second_half.reverse
  (List.range n).map (fun i => 
    if i % 2 = 0 then 
      first_half[i / 2]!
    else 
      rev_second_half[(i - 1) / 2]!)

-- LLM HELPER
lemma merge_sort_perm (lst: List Int): List.Perm lst lst.mergeSort := by
  exact List.perm_mergeSort lst

-- LLM HELPER
lemma implementation_length (lst: List Int): (implementation lst).length = lst.length := by
  simp [implementation]
  rw [List.length_map, List.length_range]

-- LLM HELPER  
lemma implementation_perm (lst: List Int): List.Perm lst (implementation lst) := by
  let sorted_lst := lst.mergeSort
  have h1: List.Perm lst sorted_lst := merge_sort_perm lst
  have h2: List.Perm sorted_lst (implementation lst) := by
    simp [implementation]
    apply List.Perm.refl
  exact List.Perm.trans h1 h2

-- LLM HELPER
lemma even_index_correct (lst: List Int) (i: Nat) 
  (hi: 0 <= i ∧ i < lst.length ∧ i % 2 = 0): 
  (implementation lst)[i]! = lst.mergeSort[i / 2]! := by
  simp [implementation]
  rw [List.get_map, List.get_range]
  simp [hi.2.2]
  rfl

-- LLM HELPER
lemma odd_index_correct (lst: List Int) (i: Nat) 
  (hi: 0 <= i ∧ i < lst.length ∧ i % 2 = 1): 
  (implementation lst)[i]! = lst.mergeSort[lst.length - (i-1)/2 - 1]! := by
  simp [implementation]
  rw [List.get_map, List.get_range]
  simp [hi.2.2]
  rfl

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · constructor
    · exact implementation_perm lst
    · constructor
      · intro i hi
        exact even_index_correct lst i hi
      · intro i hi
        exact odd_index_correct lst i hi