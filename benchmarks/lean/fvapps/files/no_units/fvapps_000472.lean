-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mct_from_leaf_values (arr : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem base_cases :
  mct_from_leaf_values [] = 0 ∧
  mct_from_leaf_values [5] = 0 ∧ 
  mct_from_leaf_values [4, 11] = 44 :=
  sorry
-- </vc-theorems>