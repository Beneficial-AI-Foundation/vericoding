import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List Int → Int)
-- inputs
(lst : List Int) :=
-- spec
let spec (result : Int) :=
let last := lst.length-1;
(lst = [] → result = 0) ∧
(lst ≠ [] ∧ last % 3 = 0 → result = lst[last]! ^ 2 + impl (lst.take last)) ∧
(lst ≠ [] ∧ last % 4 = 0 ∧ last % 3 != 0 → result = lst[last]! ^ 3 + impl (lst.take last)) ∧
(lst ≠ [] ∧ last % 3 != 0 ∧ last % 4 != 0 → result = lst[last]! + impl (lst.take last))
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma list_take_length_lt (lst : List Int) (h : lst ≠ []) : (lst.take (lst.length - 1)).length < lst.length := by
  cases' lst with head tail
  · contradiction
  · simp [List.take, List.length]
    cases' tail with head' tail'
    · simp
    · simp [List.length]
      rw [List.take_length]
      simp [min_def]
      split_ifs
      · omega
      · omega

def implementation (lst : List Int) : Int := 
  match lst with
  | [] => 0
  | _ => 
    let last := lst.length - 1
    let last_elem := lst[last]!
    if last % 3 = 0 then
      last_elem ^ 2 + implementation (lst.take last)
    else if last % 4 = 0 then
      last_elem ^ 3 + implementation (lst.take last)
    else
      last_elem + implementation (lst.take last)
termination_by implementation lst => lst.length

theorem correctness
(lst : List Int)
: problem_spec implementation lst := by
  unfold problem_spec
  let spec := fun result => 
    let last := lst.length - 1
    (lst = [] → result = 0) ∧
    (lst ≠ [] ∧ last % 3 = 0 → result = lst[last]! ^ 2 + implementation (lst.take last)) ∧
    (lst ≠ [] ∧ last % 4 = 0 ∧ last % 3 ≠ 0 → result = lst[last]! ^ 3 + implementation (lst.take last)) ∧
    (lst ≠ [] ∧ last % 3 ≠ 0 ∧ last % 4 ≠ 0 → result = lst[last]! + implementation (lst.take last))
  
  use implementation lst
  constructor
  · rfl
  · constructor
    · intro h
      unfold implementation
      simp [h]
    · constructor
      · intro ⟨h_ne, h_mod3⟩
        unfold implementation
        simp [h_ne]
        rw [if_pos h_mod3]
      · constructor
        · intro ⟨h_ne, h_mod4, h_not_mod3⟩
          unfold implementation
          simp [h_ne]
          rw [if_neg h_not_mod3, if_pos h_mod4]
        · intro ⟨h_ne, h_not_mod3, h_not_mod4⟩
          unfold implementation
          simp [h_ne]
          rw [if_neg h_not_mod3, if_neg h_not_mod4]