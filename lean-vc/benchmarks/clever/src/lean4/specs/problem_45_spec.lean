import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: Rat → Rat → Rat)
(a h: Rat) :=
let spec (result: Rat) :=
  a = 0 → result = 0 ∧
  (a ≠ 0 → (2 * result) / a = h);
∃ result, implementation a h = result ∧
spec result

def implementation (a h: Rat) : Rat := sorry

theorem correctness
(a h : Rat)
: problem_spec implementation a h := sorry 