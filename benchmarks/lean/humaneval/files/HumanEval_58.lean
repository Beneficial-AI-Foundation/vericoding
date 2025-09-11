-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (l1 l2: List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List Int → List Int → List Int)
-- inputs
(l1 l2: List Int) :=
let is_unique (result: List Int) :=
  ∀ i j, i < result.length → j < result.length →
  i ≠ j → result[i]! ≠ result[j]!;
let is_sorted (result: List Int) :=
  ∀ i, i < result.length - 1 →
  result[i]! ≤ result[i + 1]!;
-- spec
let spec (result: List Int) :=
  is_unique result ∧
  is_sorted result ∧
  (∀ i : Int, i ∈ result ↔ i ∈ l1 ∧ i ∈ l2)
-- program termination
∃ result, implementation l1 l2 = result ∧
spec result

theorem correctness
(l1 l2: List Int)
: problem_spec implementation l1 l2
:= by
  sorry
-- </vc-theorems>

-- #test implementation [1, 4, 3, 34, 653, 2, 5] [5, 7, 1, 5, 9, 653, 121] = [1, 5, 653]
-- #test implementation [5, 3, 2, 8] [3, 2] = [2, 3]