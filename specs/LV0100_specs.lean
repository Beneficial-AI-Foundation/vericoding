-- <vc-preamble>
import Std.Data.HashSet

@[reducible, simp]
def uniqueProduct_precond (arr : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def uniqueProduct (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def uniqueProduct_postcond (arr : Array Int) (result: Int) (h_precond : uniqueProduct_precond (arr)) :=
  result - (arr.toList.eraseDups.foldl (· * ·) 1) = 0 ∧
  (arr.toList.eraseDups.foldl (· * ·) 1) - result = 0

theorem uniqueProduct_spec_satisfied (arr: Array Int) (h_precond : uniqueProduct_precond (arr)) :
    uniqueProduct_postcond (arr) (uniqueProduct (arr) h_precond) h_precond := by
  sorry
-- </vc-theorems>