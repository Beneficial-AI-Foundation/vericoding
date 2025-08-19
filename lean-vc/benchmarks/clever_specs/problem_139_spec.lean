import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
let factorial := Nat.factorial n;
(0 < n → result / factorial = impl (n - 1)) ∧
(n = 0 → result = 1);
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

def implementation (n: Nat) : Nat := sorry

theorem correctness
(n: Nat)
: problem_spec implementation n := sorry
