-- <vc-helpers>
-- </vc-helpers>

def abs (n : Int) : Int := sorry
def min_change_to_equal_leaves (target : Int) (leaf_values : List Int) : Int := sorry

theorem min_change_empty_list {target : Int} (h : target ≥ 0) :
  min_change_to_equal_leaves target [] = 0 := sorry

theorem min_change_single_leaf {target : Int} (h : target ≥ 0) :
  min_change_to_equal_leaves target [target] = 0 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval min_change_to_equal_leaves 30 [26, 26, 36, 26]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_change_to_equal_leaves 10 [10, 10, 10]

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_change_to_equal_leaves 6 [4, 8]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible