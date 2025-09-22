-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (arr: List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(arr: List Int) :=

-- spec
let spec (result: Int) :=
  let dig_sum (x: Int): Int :=
    let digs := x.natAbs.digits 10;
    if x >= 0 then
      (List.map (fun t => (t: Int)) digs).sum
    else
      (List.map (fun t => (t: Int)) (digs.drop 1)).sum - (digs[0]! : Int);
  (arr = [] → result = 0) ∧
  (arr ≠ [] → 0 < (dig_sum arr[0]!) → result = 1 + implementation (arr.drop 1)) ∧
  (arr ≠ [] → (dig_sum arr[0]!) ≤ 0 → result = implementation (arr.drop 1));
-- program termination
∃ result, implementation arr = result ∧
spec result

theorem correctness
(arr: List Int)
: problem_spec implementation arr
:= by
  sorry
-- </vc-theorems>