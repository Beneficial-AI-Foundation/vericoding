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

-- LLM HELPER
lemma getD_eq_get (lst : List Int) (h : lst ≠ []) : lst[lst.length - 1]?.getD 0 = lst[lst.length - 1]! := by
  simp [List.getD, List.get!]
  rw [List.get?_eq_get]
  simp [List.get]
  split_ifs with h_bounds
  · rfl
  · exfalso
    cases' lst with head tail
    · contradiction
    · simp [List.length] at h_bounds
      omega

-- LLM HELPER
lemma ne_to_not_eq (a b : Nat) : (a != b) = true → ¬(a = b) := by
  intro h
  simp at h
  exact h

def implementation (lst : List Int) : Int := 
  match lst with
  | [] => 0
  | _ => 
    let last := lst.length - 1
    let last_elem := lst[last]?.getD 0
    if last % 3 = 0 then
      last_elem ^ 2 + implementation (lst.take last)
    else if last % 4 = 0 then
      last_elem ^ 3 + implementation (lst.take last)
    else
      last_elem + implementation (lst.take last)
termination_by lst.length
decreasing_by
  all_goals simp_wf
  all_goals {
    apply list_take_length_lt
    cases' lst with head tail
    · contradiction
    · simp
  }

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
      simp [implementation, h]
    · constructor
      · intro ⟨h_ne, h_mod3⟩
        simp [implementation, h_ne]
        rw [if_pos h_mod3]
        rw [getD_eq_get _ h_ne]
      · constructor
        · intro ⟨h_ne, h_mod4, h_not_mod3⟩
          simp [implementation, h_ne]
          rw [if_neg h_not_mod3]
          rw [if_pos h_mod4]
          rw [getD_eq_get _ h_ne]
        · intro ⟨h_ne, h_not_mod3, h_not_mod4⟩
          simp [implementation, h_ne]
          rw [if_neg h_not_mod3]
          rw [if_neg h_not_mod4]
          rw [getD_eq_get _ h_ne]