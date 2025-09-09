def maximum (xs: List Int) : Int := match xs with
  | [] => 0
  | h::t => t.foldl max h

def minimum (xs: List Int) : Int := match xs with
  | [] => 0
  | h::t => t.foldl min h

-- <vc-helpers>
-- </vc-helpers>

def smallestRangeII (nums: List Int) (k: Int) : Int := sorry

theorem result_nonnegative (nums: List Int) (k: Int) (h: k ≥ 0) :
  smallestRangeII nums k ≥ 0 := sorry

theorem single_element_gives_zero (x: Int) (k: Int) :
  smallestRangeII [x] k = 0 := sorry

theorem empty_list_gives_zero (k: Int) :
  smallestRangeII [] k = 0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval smallestRangeII [1] 0

/-
info: 6
-/
-- #guard_msgs in
-- #eval smallestRangeII [0, 10] 2

/-
info: 3
-/
-- #guard_msgs in
-- #eval smallestRangeII [1, 3, 6] 3

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible