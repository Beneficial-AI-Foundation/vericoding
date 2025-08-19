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

theorem correctness
(a b c: Nat)
: problem_spec implementation a b c := by
  simp [problem_spec]
  use implementation a b c
  constructor
  · rfl
  · intro ha hb hc
    simp [implementation]
    constructor
    · simp [List.length_cons, List.length_nil]
    · constructor
      · intro h_le
        simp [h_le]
        constructor
        · simp [List.getElem_cons_zero]
          omega
        · simp [List.getElem_cons_one]
          omega
      · intro h_lt
        simp [h_lt]
        constructor
        · simp [List.getElem_cons_zero]
          omega
        · simp [List.getElem_cons_one]