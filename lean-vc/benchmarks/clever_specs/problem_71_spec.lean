import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

def problem_spec
(implementation: Rat → Rat → Rat → Rat)
(a: Rat) (b: Rat) (c: Rat) :=
let spec (result : Rat) :=
  let is_valid_triangle :=
    (a + b > c) ∧  (a + c > b) ∧ (b + c > a);
  let s :=
    (a + b + c) / 2;
  if is_valid_triangle then
    |result^2 - (s * (s-a) * (s-b) * (s-c))| ≤ ((1: Rat)/10000)
  else
    result = -1
∃ result, implementation a b c = result ∧
spec result

def implementation (a: Rat) (b: Rat) (c: Rat): Rat := sorry

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c := sorry 