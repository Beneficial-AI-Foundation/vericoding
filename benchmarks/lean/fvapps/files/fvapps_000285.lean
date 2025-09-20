-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxAbsValExpr (arr1 arr2 : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxAbsValExpr_non_negative {arr1 arr2 : List Int} 
  (h : arr1.length = arr2.length) :
  maxAbsValExpr arr1 arr2 ≥ 0 :=
sorry

theorem maxAbsValExpr_constant_invariant {arr1 arr2 : List Int} (const : Int)
  (h : arr1.length = arr2.length) :
  maxAbsValExpr (arr1.map (· + const)) (arr2.map (· + const)) = maxAbsValExpr arr1 arr2 :=
sorry
-- </vc-theorems>