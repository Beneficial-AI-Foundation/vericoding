-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (arr: List Int) (k: Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(impl: List Int → Int → List Int)
-- inputs
(arr: List Int)
(k: Int) :=
-- spec
let spec (result: List Int) :=
    1 ≤ arr.length → arr.length ≤ 1000 → arr.all (fun x => -1000 ≤ x ∧ x ≤ 1000) → 0 ≤ k → k ≤ arr.length →
    result.length = k ∧
    result.Sorted (· ≤ ·) ∧
    ∀ x ∈ result, x ∈ arr ∧

    let result_reversed := result.reverse; -- reverse to get last element
    match result_reversed with
    | [] => k = 0
    | max :: remaining_reversed =>
      arr.max? = some max ∧
      impl (arr.erase max) (k-1) = (remaining_reversed.reverse)
-- program terminates
∃ result, impl arr k = result ∧
-- return value satisfies spec
spec result

theorem correctness
(arr: List Int)
(k: Int)
: problem_spec implementation arr k  := by
  sorry
-- </vc-theorems>