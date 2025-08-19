import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Nat → Nat → Nat → Bool)
-- inputs
(a b c: Nat) :=
-- spec
let spec (result: Bool) :=
result ↔
  0 < a ∧ 0 < b ∧ 0 < c ∧
  ((a * a + b * b = c * c) ∨
  (a * a + c * c = b * b) ∨
  (b * b + c * c = a * a))
-- program terminates
∃ result, impl a b c = result ∧
-- return value satisfies spec
spec result

def implementation (a b c: Nat) : Bool := 
  0 < a && 0 < b && 0 < c && 
  (a * a + b * b == c * c || 
   a * a + c * c == b * b || 
   b * b + c * c == a * a)

theorem correctness
(a b c: Nat)
: problem_spec implementation a b c := by
  unfold problem_spec
  use (0 < a && 0 < b && 0 < c && 
       (a * a + b * b == c * c || 
        a * a + c * c == b * b || 
        b * b + c * c == a * a))
  constructor
  · rfl
  · unfold implementation
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    constructor
    · intro h
      cases' h with h_pos h_pyth
      exact ⟨h_pos, h_pyth⟩
    · intro h
      cases' h with h_pos h_pyth
      exact ⟨h_pos, h_pyth⟩