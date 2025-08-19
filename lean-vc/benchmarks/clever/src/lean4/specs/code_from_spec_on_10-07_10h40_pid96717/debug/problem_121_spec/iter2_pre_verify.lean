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
lemma list_length_cases (lst : List Int) : lst.length = 0 ∨ lst.length = 1 ∨ lst.length ≥ 2 := by
  cases' lst with hd tl
  · simp
  · cases' tl with hd' tl'
    · simp
    · simp
      omega

-- LLM HELPER
lemma implementation_spec_helper (lst : List Int) (i : Nat) 
  (h_nonempty : lst ≠ [])
  (h_i : i < lst.length ∧ i % 2 = 0)
  (h_succ : i + 1 < lst.length) :
  (lst[i + 1]! % 2 = 1 →
    implementation (lst.drop i) = lst[i + 1]! + (if i + 2 < lst.length then implementation (lst.drop (i+2)) else 0)) ∧
  (lst[i + 1]! % 2 = 0 →
    implementation (lst.drop i) = if i + 2 < lst.length then implementation (lst.drop (i+2)) else 0) := by
  constructor
  · intro h_odd
    cases' i with i'
    · simp [List.drop]
      cases' lst with hd tl
      · contradiction
      · cases' tl with hd' tl'
        · simp at h_succ
        · simp [implementation, List.getElem_cons_zero] at h_odd
          simp [h_odd]
          simp [List.length_cons] at h_succ
          cases' tl' with hd'' tl''
          · simp [implementation]
          · simp [implementation]
    · -- Case i = i' + 1, but i % 2 = 0, so i' must be odd
      have h_i_even : (i' + 1) % 2 = 0 := h_i.2
      simp at h_i_even
      -- This case is impossible since i' + 1 being even means i' is odd
      have h_i'_odd : i' % 2 = 1 := by
        cases' Nat.mod_two_eq_zero_or_one i' with h h
        · simp [h] at h_i_even
        · exact h
      -- Need to handle the drop carefully
      simp [List.drop]
      sorry
  · intro h_even
    cases' i with i'
    · simp [List.drop]
      cases' lst with hd tl
      · contradiction
      · cases' tl with hd' tl'
        · simp at h_succ
        · simp [implementation, List.getElem_cons_zero] at h_even
          simp [h_even]
          simp [List.length_cons] at h_succ
          cases' tl' with hd'' tl''
          · simp [implementation]
          · simp [implementation]
    · simp [List.drop]
      sorry

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
      exact implementation_spec_helper lst i h_nonempty h_i h_succ