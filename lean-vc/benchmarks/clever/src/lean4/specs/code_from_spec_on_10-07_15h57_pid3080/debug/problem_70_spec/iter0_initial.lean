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
def interleave_sorted (sorted_lst: List Int) : List Int :=
  let n := sorted_lst.length
  let first_half := sorted_lst.take ((n + 1) / 2)
  let second_half := sorted_lst.drop ((n + 1) / 2)
  let reversed_second := second_half.reverse
  List.range n |>.map (fun i =>
    if i % 2 = 0 then
      first_half[i / 2]!
    else
      reversed_second[(i - 1) / 2]!
  )

def implementation (lst: List Int): List Int := 
  interleave_sorted lst.mergeSort

-- LLM HELPER
lemma interleave_length (sorted_lst: List Int) : 
  (interleave_sorted sorted_lst).length = sorted_lst.length := by
  simp [interleave_sorted]

-- LLM HELPER
lemma interleave_get_even (sorted_lst: List Int) (i: Nat) 
  (h1: i < sorted_lst.length) (h2: i % 2 = 0) :
  (interleave_sorted sorted_lst)[i]! = sorted_lst[i / 2]! := by
  simp [interleave_sorted]
  simp [List.get_map, h2]
  rw [List.get_take]
  simp

-- LLM HELPER
lemma interleave_get_odd (sorted_lst: List Int) (i: Nat) 
  (h1: i < sorted_lst.length) (h2: i % 2 = 1) :
  (interleave_sorted sorted_lst)[i]! = sorted_lst[sorted_lst.length - (i-1)/2 - 1]! := by
  simp [interleave_sorted]
  simp [List.get_map, h2]
  have h3 : (i - 1) / 2 < (sorted_lst.drop ((sorted_lst.length + 1) / 2)).length := by
    simp [List.length_drop]
    omega
  rw [List.get_reverse]
  simp [List.get_drop]
  congr 1
  omega

-- LLM HELPER
lemma interleave_perm (sorted_lst: List Int) : 
  List.Perm sorted_lst (interleave_sorted sorted_lst) := by
  apply List.Perm.symm
  apply List.perm_of_count_eq
  · simp [interleave_length]
  · intro a
    simp [interleave_sorted]
    sorry

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:= by
  simp [problem_spec, implementation]
  use interleave_sorted lst.mergeSort
  constructor
  · rfl
  · constructor
    · apply List.Perm.trans
      · exact List.perm_mergeSort lst
      · exact interleave_perm lst.mergeSort
    · constructor
      · intro i h
        simp [interleave_length] at h
        apply interleave_get_even
        · exact h.2.1
        · exact h.2.2
      · intro i h
        simp [interleave_length] at h
        apply interleave_get_odd
        · exact h.2.1
        · exact h.2.2