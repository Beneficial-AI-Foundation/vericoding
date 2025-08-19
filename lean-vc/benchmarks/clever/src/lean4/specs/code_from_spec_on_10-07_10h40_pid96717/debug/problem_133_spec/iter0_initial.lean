import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List Rat → Int)
-- inputs
(lst: List Rat) :=
-- spec
let spec (result: Int) :=
  (lst = [] → result = 0) ∧
  (lst != [] → 0 ≤ result - lst[0]!.ceil^2 ∧ (impl (lst.drop 1) = (result - lst[0]!.ceil^2)))
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

def implementation (lst: List Rat) : Int := 
  match lst with
  | [] => 0
  | x :: xs => x.ceil^2 + implementation xs

-- LLM HELPER
lemma list_not_empty_iff {α : Type*} (l : List α) : l ≠ [] ↔ ∃ x xs, l = x :: xs := by
  constructor
  · intro h
    cases' l with x xs
    · exact (h rfl).elim
    · exact ⟨x, xs, rfl⟩
  · intro ⟨x, xs, h⟩
    rw [h]
    simp

-- LLM HELPER
lemma list_head_tail_eq {α : Type*} (l : List α) (h : l ≠ []) : 
  l = l[0]! :: l.drop 1 := by
  cases' l with x xs
  · exact (h rfl).elim
  · simp [List.getElem_cons_zero, List.drop_one]

-- LLM HELPER
lemma implementation_recurrence (x : Rat) (xs : List Rat) :
  implementation (x :: xs) = x.ceil^2 + implementation xs := by
  simp [implementation]

theorem correctness
(lst: List Rat)
: problem_spec implementation lst := by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · intro result h_eq
    rw [← h_eq]
    constructor
    · intro h_empty
      rw [h_empty]
      simp [implementation]
    · intro h_not_empty
      have ⟨x, xs, h_cons⟩ := list_not_empty_iff.mp h_not_empty
      rw [h_cons]
      constructor
      · simp [implementation_recurrence]
        simp [Int.sub_self]
      · simp [List.getElem_cons_zero, List.drop_one]
        rw [implementation_recurrence]
        ring