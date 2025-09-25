-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (lst: List Int) : Option Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List Int → Option Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result : Option Int) :=
  match result with
  | none => ¬ (∃ i j, i < lst.length ∧ j < lst.length ∧ i ≠ j ∧ lst[i]! < lst[j]!)
  | some result =>
    let smaller_els := lst.filter (· < result);
    0 < smaller_els.length ∧
    smaller_els.all (λ x => x = smaller_els[0]!);
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:= by
  sorry
-- </vc-theorems>