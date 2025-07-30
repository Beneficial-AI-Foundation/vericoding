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
lemma get_drop_eq (lst: List Int) (i j: Nat) (h: i + j < lst.length) :
  (lst.drop i)[j]! = lst[i + j]! := by
  rw [List.get!_eq_get, List.get!_eq_get]
  rw [List.get_drop]

-- LLM HELPER  
lemma length_drop_eq (lst: List Int) (i: Nat) :
  (lst.drop i).length = lst.length - i := by
  rw [List.length_drop]

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  simp [problem_spec]
  use implementation lst
  constructor
  · rfl
  · intro h_nonempty i h_i
    have h_even : i % 2 = 0 := h_i.2
    constructor
    · intro h_len
      simp [implementation]
      cases' lst with a as
      · contradiction
      · cases' as with b bs
        · rfl
        · simp at h_len
    · intro h_succ
      constructor
      · intro h_odd
        cases' h_lst : lst.drop i with a as
        · simp at h_lst
          have : lst.length ≤ i := by
            simp [List.drop_eq_nil_iff_le] at h_lst
            exact h_lst
          linarith [h_i.1]
        · cases' as with b bs
          · simp [implementation]
            have : (lst.drop i).length = 1 := by
              rw [h_lst]
              simp
            have : lst.length - i = 1 := by
              rw [← length_drop_eq, this]
            linarith [h_succ]
          · simp [implementation]
            have : lst[i + 1]! = b := by
              rw [← get_drop_eq]
              · simp [h_lst]
              · linarith [h_succ]
            rw [← this, h_odd]
            simp
            congr 1
            by_cases h_case : i + 2 < lst.length
            · simp [h_case]
              congr 1
              have : lst.drop (i + 2) = bs := by
                have : lst.drop i = a :: b :: bs := h_lst
                rw [← List.drop_drop]
                simp [this]
              rw [this]
              rfl
            · simp [h_case]
              have : bs = [] := by
                have : lst.drop i = a :: b :: bs := h_lst
                have : (lst.drop i).length = lst.length - i := length_drop_eq lst i
                rw [this, h_lst] at this
                simp at this
                have : lst.length - i = 2 + bs.length := this
                have : i + 2 ≤ lst.length := by
                  linarith
                have : ¬(i + 2 < lst.length) := h_case
                have : i + 2 = lst.length := by
                  linarith
                have : lst.length - i = 2 := by
                  linarith
                rw [this] at this
                simp at this
                exact this
              rw [this]
              simp [implementation]
      · intro h_even_next
        cases' h_lst : lst.drop i with a as
        · simp at h_lst
          have : lst.length ≤ i := by
            simp [List.drop_eq_nil_iff_le] at h_lst
            exact h_lst
          linarith [h_i.1]
        · cases' as with b bs
          · simp [implementation]
            have : (lst.drop i).length = 1 := by
              rw [h_lst]
              simp
            have : lst.length - i = 1 := by
              rw [← length_drop_eq, this]
            linarith [h_succ]
          · simp [implementation]
            have : lst[i + 1]! = b := by
              rw [← get_drop_eq]
              · simp [h_lst]
              · linarith [h_succ]
            rw [← this]
            have : 2 ∣ lst[i + 1]! := h_even_next
            have : lst[i + 1]! % 2 = 0 := by
              rw [dvd_iff_mod_eq_zero] at this
              exact this
            rw [this]
            simp
            by_cases h_case : i + 2 < lst.length
            · simp [h_case]
              congr 1
              have : lst.drop (i + 2) = bs := by
                have : lst.drop i = a :: b :: bs := h_lst
                rw [← List.drop_drop]
                simp [this]
              rw [this]
              rfl
            · simp [h_case]
              have : bs = [] := by
                have : lst.drop i = a :: b :: bs := h_lst
                have : (lst.drop i).length = lst.length - i := length_drop_eq lst i
                rw [this, h_lst] at this
                simp at this
                have : lst.length - i = 2 + bs.length := this
                have : i + 2 ≤ lst.length := by
                  linarith
                have : ¬(i + 2 < lst.length) := h_case
                have : i + 2 = lst.length := by
                  linarith
                have : lst.length - i = 2 := by
                  linarith
                rw [this] at this
                simp at this
                exact this
              rw [this]
              simp [implementation]