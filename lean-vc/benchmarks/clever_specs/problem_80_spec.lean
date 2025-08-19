import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → Bool)
-- inputs
(s: String) :=
-- spec
let spec (result : Bool) :=
  result ↔
  (3 ≤ s.length) ∧
  ¬ (∃ i j, i < j ∧ j < s.length ∧ j - i ≤ 2 ∧ s.data.get! i = s.data.get! j)
-- program termination
∃ result,
  implementation s = result ∧
  spec result

def implementation (s: String) : Bool := sorry

theorem correctness
(s: String)
: problem_spec implementation s
:= sorry
