import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(nums: List Int) :=
-- spec
let spec (result : Int) :=
  (∀ subarray ∈ nums.sublists,
    subarray.length > 0 →
    result ≤ subarray.sum) ∧
  (∃ subarray ∈ nums.sublists,
    subarray.length > 0 ∧
    result = subarray.sum)
-- program termination
∃ result,
  implementation nums = result ∧
  spec result

-- <vc-helpers>

-- </vc-helpers>

-- <vc-description>
/-
function_signature: "def minSubArraySum(nums : list[int]) -> int"
docstring: |
    Given an array of integers nums, find the minimum sum of any non-empty sub-array
    of nums.
test_cases:
  - input: [2, 3, 4, 1, 2, 4]
    expected_output: 1
  - input: [-1, -2, -3]
    expected_output: -6
-/
-- </vc-description>

-- <vc-spec>
def implementation (nums: List Int) : Int :=
-- </vc-spec>
-- <vc-code>
sorry
-- </vc-code>

-- <vc-theorem>
theorem correctness
(nums: List Int)
: problem_spec implementation nums
:=
-- </vc-theorem>
-- <vc-proof>
by
  sorry
-- </vc-proof>

-- #test implementation [2, 3, 4, 1, 2, 4] = 1
-- #test implementation [-1, -2, -3] = -6