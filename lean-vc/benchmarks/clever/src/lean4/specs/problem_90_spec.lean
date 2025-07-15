import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → Option Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result : Option Int) :=
  match result with
  | none => ¬ (∃ i j, i < lst.length ∧ j < lst.length ∧ i ≠ j ∧ lst.get! i < lst.get! j)
  | some result =>
    let smaller_els := lst.filter (· < result);
    0 < smaller_els.length ∧
    smaller_els.all (λ x => x = smaller_els.get! 0);
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

def implementation (lst: List Int) : Option Int := sorry

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:= sorry
