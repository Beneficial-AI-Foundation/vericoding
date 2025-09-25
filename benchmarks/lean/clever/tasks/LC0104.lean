-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (arr: List Int) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List Int → List String)
-- inputs
(arr: List Int) :=
-- spec
let spec (result: List String) :=
  let digits: List String := ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"];
  (forall s: String, (s ∈ result → s ∈ digits)) ∧
  (arr.length ≥ result.length) ∧
  (forall x: Nat, ((x: Int) ∈ arr ∧ 1 ≤ x ∧ x ≤ 9) → (digits[x-1]! ∈ result)) ∧
  (List.Sorted Int.le (List.map (fun (s: String) => (List.idxOf s digits) + 1) result).reverse)
-- program termination
∃ result, implementation arr = result ∧
spec result

theorem correctness
(arr: List Int)
: problem_spec implementation arr
:= by
  sorry
-- </vc-theorems>