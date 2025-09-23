-- <vc-preamble>
import Mathlib

@[reducible]
def maxStrength_precond (nums : List Int) : Prop :=
  nums ≠ []
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxStrength (nums : List Int) (h_precond : maxStrength_precond (nums)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def maxStrength_postcond (nums : List Int) (result: Int) (h_precond : maxStrength_precond (nums)) : Prop :=
  let sublists := nums.sublists.filter (· ≠ [])
  let products := sublists.map (List.foldl (· * ·) 1)
  products.contains result ∧ products.all (· ≤ result)

theorem maxStrength_spec_satisfied (nums: List Int) (h_precond : maxStrength_precond (nums)) :
    maxStrength_postcond (nums) (maxStrength (nums) h_precond) h_precond := by
  sorry
-- </vc-theorems>