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

-- LLM HELPER
lemma implementation_drop_succ_succ (a b : Int) (rest : List Int) :
  implementation (b :: rest) = (if b % 2 = 1 then b + implementation rest else implementation rest) := by
  simp [implementation]

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · intro h_nonempty i h_i
    constructor
    · intro h_len_one
      cases' lst with head tail
      · contradiction
      · cases' tail with head2 tail2
        · rfl
        · simp at h_len_one
    · intro h_succ
      cases' lst with head tail
      · contradiction
      · cases' tail with head2 tail2
        · simp at h_succ
          omega
        · constructor
          · intro h_odd
            simp [List.drop]
            rw [List.get_cons_succ, List.get_cons_zero]
            rw [implementation_drop_succ_succ]
            simp [h_odd]
            congr 1
            cases' tail2 with head3 tail3
            · simp
            · simp [implementation]
          · intro h_even
            simp [List.drop]
            rw [List.get_cons_succ, List.get_cons_zero]
            rw [implementation_drop_succ_succ]
            simp [h_even]
            cases' tail2 with head3 tail3
            · simp
            · simp [implementation]