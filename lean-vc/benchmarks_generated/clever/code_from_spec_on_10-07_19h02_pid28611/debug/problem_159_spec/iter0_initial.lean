import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Nat → Nat → Nat → List Nat)
-- inputs
(number need remaining: Nat) :=
-- spec
let spec (result: List Nat) :=
number ≤ 1000 → need ≤ 1000 → remaining ≤ 1000 →
result.length = 2 ∧
(need ≤ remaining → result[0]! - need = number ∧
need = remaining - result[1]!) ∧
(remaining < need → result[0]! - remaining = number ∧
result[1]! = 0);
-- program terminates
∃ result, impl number need remaining = result ∧
-- return value satisfies spec
spec result

def implementation (a b c: Nat) : List Nat := 
  if b ≤ c then
    [a + b, c - b]
  else
    [a + c, 0]

-- LLM HELPER
lemma list_get_elem_implementation_case1 (a b c : Nat) (h : b ≤ c) :
  (implementation a b c)[0]! = a + b ∧ (implementation a b c)[1]! = c - b := by
  simp [implementation, h]

-- LLM HELPER
lemma list_get_elem_implementation_case2 (a b c : Nat) (h : ¬b ≤ c) :
  (implementation a b c)[0]! = a + c ∧ (implementation a b c)[1]! = 0 := by
  simp [implementation, h]

-- LLM HELPER
lemma implementation_length (a b c : Nat) : (implementation a b c).length = 2 := by
  simp [implementation]
  split_ifs <;> rfl

theorem correctness
(a b c: Nat)
: problem_spec implementation a b c := by
  use implementation a b c
  constructor
  · rfl
  · intro ha hb hc
    constructor
    · exact implementation_length a b c
    · constructor
      · intro h_need_le_remaining
        have h1 := list_get_elem_implementation_case1 a b c h_need_le_remaining
        constructor
        · rw [h1.1]
          simp
        · rw [h1.2]
          simp
      · intro h_remaining_lt_need
        have h_not_le : ¬b ≤ c := by
          rw [not_le]
          exact h_remaining_lt_need
        have h1 := list_get_elem_implementation_case2 a b c h_not_le
        constructor
        · rw [h1.1]
          simp
        · exact h1.2