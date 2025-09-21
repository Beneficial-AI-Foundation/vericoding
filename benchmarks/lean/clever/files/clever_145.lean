-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

/--
name: digit_sum
use: |
  Helper to sum the digits of a number. If the number is negative, the
  negative sign is treated as part of the first digit.
problems:
  - 145
-/
def digit_sum (n : Int) : Int :=
  let ds := (toString n.natAbs).toList.map fun c => c.toNat - Char.toNat '0'
  match ds with
  | [] => 0
  | d :: ds' =>
    let tail := ds'.foldl (· + ·) 0
    if n < 0 then Int.ofNat tail - Int.ofNat d
    else Int.ofNat (d + tail)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (nums: List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(impl: List Int → List Int)
-- inputs
(nums: List Int) :=
-- spec
let spec (result: List Int) :=
List.Perm nums result ∧
match result with
| [] => nums = []
| head::tail =>
  let head_sum := digit_sum head;
  (∀ num ∈ nums,
    let sum := digit_sum num;
    sum > head_sum ∨
   (sum = head_sum ∧ nums.idxOf num ≥ nums.idxOf head))
  ∧ impl (nums.erase head) = tail
-- program termination
∃ result, impl nums = result ∧
-- return value satisfies spec
spec result

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  sorry
-- </vc-theorems>