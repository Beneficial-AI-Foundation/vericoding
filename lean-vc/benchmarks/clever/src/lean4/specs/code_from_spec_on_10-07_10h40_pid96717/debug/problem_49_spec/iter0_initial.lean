import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → Nat → Nat)
-- inputs
(n p: Nat) :=
-- spec
let spec (result: Nat) :=
0 < p ∧
result < p ∧
(∃ k : Nat, p * k + result = Nat.pow 2 n)
-- program termination
∃ result, implementation n p = result ∧
spec result

def implementation (n p: Nat) : Nat := (2^n) % p

theorem correctness
(n p: Nat)
: problem_spec implementation n p
:= by
  unfold problem_spec
  simp only [implementation]
  use (2^n) % p
  constructor
  · rfl
  · by_cases h : p = 0
    · simp [h]
      sorry
    · have hp : 0 < p := Nat.pos_of_ne_zero h
      constructor
      · exact hp
      constructor
      · exact Nat.mod_lt (2^n) hp
      · use (2^n) / p
        exact Nat.div_add_mod (2^n) p