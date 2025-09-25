-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (arr: List Int) : Option Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(impl: List Int → Option Int)
-- inputs
(arr: List Int) :=
-- spec
let spec (result: Option Int) :=
  match result with
  | none => arr = []
  | some result =>
  let magnitude_sum := (arr.map (fun x => Int.ofNat x.natAbs)).sum;
    let neg_count_odd := (arr.filter (fun x => x < 0)).length % 2 = 1;
    let has_zero := 0 ∈ arr;
    (result < 0 ↔ (neg_count_odd ∧ ¬has_zero)
      ∧ result = magnitude_sum * -1) ∧
    (0 < result ↔ (¬neg_count_odd ∧ ¬has_zero)
      ∧ result = magnitude_sum) ∧
    (result = 0 ↔ has_zero)
-- program terminates
∃ result, impl arr = result ∧
-- return value satisfies spec
spec result

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  sorry
-- </vc-theorems>