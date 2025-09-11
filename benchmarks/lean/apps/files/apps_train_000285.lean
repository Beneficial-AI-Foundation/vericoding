-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: 13
-/
-- #guard_msgs in
-- #eval maxAbsValExpr [1, 2, 3, 4] [-1, 4, 5, 6]

/-
info: 20
-/
-- #guard_msgs in
-- #eval maxAbsValExpr [1, -2, -5, 0, 10] [0, -2, -1, -7, -4]

/-
info: 1
-/
-- #guard_msgs in
-- #eval maxAbsValExpr [1, 1] [1, 1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible