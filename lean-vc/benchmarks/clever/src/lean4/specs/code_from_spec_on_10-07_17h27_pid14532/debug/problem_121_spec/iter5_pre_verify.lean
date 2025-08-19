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
lemma implementation_cons_cons (a b : Int) (rest : List Int) :
  implementation (a :: b :: rest) = (if b % 2 = 1 then b + implementation rest else implementation rest) := by
  simp [implementation]

-- LLM HELPER
lemma list_get_zero (a : Int) (l : List Int) : (a :: l)[0]! = a := by
  simp [List.getElem_cons_zero]

-- LLM HELPER
lemma list_get_one (a b : Int) (l : List Int) : (a :: b :: l)[1]! = b := by
  simp [List.getElem_cons_succ]

-- LLM HELPER
lemma drop_zero (l : List Int) : l.drop 0 = l := by
  simp [List.drop_zero]

-- LLM HELPER
lemma drop_succ_cons (a : Int) (l : List Int) (n : ℕ) : (a :: l).drop (n + 1) = l.drop n := by
  simp [List.drop_succ_cons]

-- LLM HELPER
lemma drop_two_cons_cons (a b : Int) (rest : List Int) : (a :: b :: rest).drop 2 = rest := by
  simp [List.drop]

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
            have h_i_zero : i = 0 := by
              cases' h_i with h_i_bound h_i_mod
              interval_cases i
              · rfl
              · simp at h_i_bound
                omega
            rw [h_i_zero]
            simp [List.drop_zero]
            have h_get : (head :: head2 :: tail2)[1]! = head2 := by
              exact list_get_one head head2 tail2
            rw [implementation_cons_cons]
            simp [h_odd]
            congr 1
            have h_len_ge_two : (head :: head2 :: tail2).length ≥ 2 := by simp
            rw [h_i_zero] at h_succ
            cases' tail2 with head3 tail3
            · simp
            · simp
              rw [drop_two_cons_cons]
          · intro h_even
            have h_i_zero : i = 0 := by
              cases' h_i with h_i_bound h_i_mod
              interval_cases i
              · rfl
              · simp at h_i_bound
                omega
            rw [h_i_zero]
            simp [List.drop_zero]
            have h_get : (head :: head2 :: tail2)[1]! = head2 := by
              exact list_get_one head head2 tail2
            rw [implementation_cons_cons]
            simp [h_even]
            have h_len_ge_two : (head :: head2 :: tail2).length ≥ 2 := by simp
            rw [h_i_zero] at h_succ
            cases' tail2 with head3 tail3
            · simp
            · simp
              rw [drop_two_cons_cons]