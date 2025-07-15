import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: String → String → Bool)
-- inputs
(a b: String) :=
-- spec
let spec (result: Bool) :=
(b.length = 0 → result) ∧
(0 < b.length →
result ↔ ((b.length ≤ a.length) ∧
  (∃ i : Nat, i < b.length ∧
  let b_rotation := b.drop i ++ b.take i;
  a.containsSubstr b_rotation)));
-- program terminates
∃ result, impl a b = result ∧
-- return value satisfies spec
spec result

def implementation (a b: String) : Bool := sorry

theorem correctness
(a b: String)
: problem_spec implementation a b := sorry
