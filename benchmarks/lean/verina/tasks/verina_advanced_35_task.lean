-- <vc-preamble>
import Std.Data.HashMap
open Std

@[reducible]
def majorityElement_precond (nums : List Int) : Prop :=
  nums.length > 0 ∧ nums.any (fun x => nums.count x > nums.length / 2)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def majorityElement (nums : List Int) (h_precond : majorityElement_precond (nums)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def majorityElement_postcond (nums : List Int) (result: Int) (h_precond : majorityElement_precond (nums)) : Prop :=
  let n := nums.length
  (nums.count result) > n / 2
  ∧ ∀ x, x ≠ result → nums.count x ≤ n / 2

theorem majorityElement_spec_satisfied (nums: List Int) (h_precond : majorityElement_precond (nums)) :
    majorityElement_postcond (nums) (majorityElement (nums) h_precond) h_precond := by
  sorry
-- </vc-theorems>