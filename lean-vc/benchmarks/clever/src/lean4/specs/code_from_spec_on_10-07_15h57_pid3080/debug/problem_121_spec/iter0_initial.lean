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
  | _ :: b :: rest =>
    if b % 2 = 1 then
      b + implementation rest
    else
      implementation rest

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  unfold problem_spec
  simp [implementation]
  use implementation lst
  constructor
  · rfl
  · intro h i hi
    constructor
    · intro h_len
      simp [implementation]
      cases' lst with head tail
      · contradiction
      · cases' tail with head' tail'
        · rfl
        · simp at h_len
    · intro h_succ
      cases' lst with head tail
      · contradiction
      · cases' tail with head' tail'
        · simp at h_succ
        · simp [implementation]
          constructor
          · intro h_odd
            simp [List.drop]
            cases' i with i'
            · simp
              split_ifs with h_cond
              · simp [implementation]
                rfl
              · simp [implementation]
                rfl
            · simp at hi
              cases' i' with i''
              · simp
                split_ifs with h_cond
                · simp [implementation]
                  rfl
                · simp [implementation]
                  rfl
              · simp
                split_ifs with h_cond
                · simp [implementation]
                  rfl
                · simp [implementation]
                  rfl
          · intro h_even
            simp [List.drop]
            cases' i with i'
            · simp
              split_ifs with h_cond
              · simp [implementation]
                rfl
              · simp [implementation]
                rfl
            · simp at hi
              cases' i' with i''
              · simp
                split_ifs with h_cond
                · simp [implementation]
                  rfl
                · simp [implementation]
                  rfl
              · simp
                split_ifs with h_cond
                · simp [implementation]
                  rfl
                · simp [implementation]
                  rfl