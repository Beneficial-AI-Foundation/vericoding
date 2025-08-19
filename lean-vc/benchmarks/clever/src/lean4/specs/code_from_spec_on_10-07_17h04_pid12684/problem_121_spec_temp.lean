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
(lst: List Int) :=
-- spec
let spec (result : Int) :=
lst ≠ [] → ∀ i,  i < lst.length ∧ i % 2 = 0 →
  (lst.length = 1 → impl lst = 0) ∧
  (i + 1 < lst.length →
    (lst[i + 1]! % 2 = 1 →
    impl (lst.drop i) = lst[i + 1]! + (if i + 2 < lst.length then impl (lst.drop (i+2)) else 0)) ∧
    (lst[i + 1]! % 2 = 0 →
    impl (lst.drop i) = if i + 2 < lst.length then impl (lst.drop (i+2)) else 0)
  )
-- program terminates
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

def implementation (lst: List Int) : Int := 
  match lst with
  | [] => 0
  | [_] => 0
  | h :: t => 
    if t.head! % 2 = 1 then
      t.head! + implementation t.tail
    else
      implementation t.tail

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  simp [problem_spec]
  use implementation lst
  constructor
  · rfl
  · intro h_nonempty
    intro i hi
    cases' hi with h_i_lt h_i_even
    constructor
    · intro h_len_one
      cases' lst with head tail
      · contradiction
      · simp [List.length] at h_len_one
        cases' tail with t_head t_tail
        · simp [implementation]
        · simp at h_len_one
    · intro h_next_exists
      cases' lst with head tail
      · contradiction
      · simp [List.length] at h_next_exists
        cases' tail with t_head t_tail
        · simp at h_next_exists
        · simp [implementation]
          constructor
          · intro h_odd
            simp [List.getElem_cons_succ, List.drop_cons]
            cases i with
            | zero => 
              simp [List.drop_zero, List.getElem_cons_zero]
              split_ifs
              · rfl
              · rfl
            | succ n =>
              simp [List.drop_succ_cons]
              split_ifs
              · simp [List.getElem_cons_succ]
                rfl
              · simp [List.getElem_cons_succ]
                rfl
          · intro h_even
            simp [List.getElem_cons_succ, List.drop_cons]
            cases i with
            | zero => 
              simp [List.drop_zero, List.getElem_cons_zero]
              split_ifs
              · rfl
              · rfl
            | succ n =>
              simp [List.drop_succ_cons]
              split_ifs
              · simp [List.getElem_cons_succ]
                rfl
              · simp [List.getElem_cons_succ]
                rfl