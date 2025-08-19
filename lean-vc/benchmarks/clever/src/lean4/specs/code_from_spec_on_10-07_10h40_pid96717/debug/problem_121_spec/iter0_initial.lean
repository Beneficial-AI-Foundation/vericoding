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
  simp only [exists_prop]
  use implementation lst
  constructor
  · rfl
  · intro h_nonempty i h_i
    constructor
    · intro h_len_one
      simp [implementation]
      cases' lst with hd tl
      · contradiction
      · cases' tl with hd' tl'
        · simp [implementation]
        · simp at h_len_one
    · intro h_succ
      constructor
      · intro h_odd
        simp [implementation]
        cases' lst with hd tl
        · contradiction
        · cases' tl with hd' tl'
          · simp at h_succ
          · simp [List.drop]
            cases' h_i with h_i_lt h_i_even
            cases' i with i'
            · simp at h_i_even h_odd h_succ
              simp [List.getElem_cons_zero] at h_odd
              simp [List.length_cons] at h_succ
              cases' tl' with hd'' tl''
              · simp [implementation]
              · simp [implementation]
                rw [h_odd]
                simp
            · simp at h_i_even
      · intro h_even
        simp [implementation]
        cases' lst with hd tl
        · contradiction
        · cases' tl with hd' tl'
          · simp at h_succ
          · simp [List.drop]
            cases' h_i with h_i_lt h_i_even
            cases' i with i'
            · simp at h_i_even h_even h_succ
              simp [List.getElem_cons_zero] at h_even
              simp [List.length_cons] at h_succ
              cases' tl' with hd'' tl''
              · simp [implementation]
              · simp [implementation]
                rw [h_even]
                simp
            · simp at h_i_even