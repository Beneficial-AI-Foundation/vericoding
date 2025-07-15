import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Nat → Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : Nat) :=
  lst.any (fun num => Nat.Prime num) →
    result > 0 ∧ ∃ i, i < lst.length ∧ Prime (lst.get! i) ∧
    (∀ j, j < lst.length ∧ Prime (lst.get! j) → lst.get! i ≤ lst.get! j) ∧
    result = (Nat.digits 10 (lst.get! i)).sum
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

def implementation (lst: List Nat) : Nat := sorry

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:= sorry
