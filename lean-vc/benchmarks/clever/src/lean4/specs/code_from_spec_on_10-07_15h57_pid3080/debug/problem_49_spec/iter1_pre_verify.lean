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
  simp [problem_spec]
  use (2^n) % p
  constructor
  · rfl
  · simp
    constructor
    · sorry -- need p > 0 assumption
    · constructor
      · exact Nat.mod_lt (2^n) (by sorry) -- need p > 0 assumption
      · use (2^n) / p
        exact Nat.div_add_mod (2^n) p