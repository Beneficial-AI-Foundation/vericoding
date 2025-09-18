-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (n : Int) : Int := sorry
def min_change_to_equal_leaves (target : Int) (leaf_values : List Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_change_empty_list {target : Int} (h : target ≥ 0) :
  min_change_to_equal_leaves target [] = 0 := sorry

theorem min_change_single_leaf {target : Int} (h : target ≥ 0) :
  min_change_to_equal_leaves target [target] = 0 := sorry
-- </vc-theorems>