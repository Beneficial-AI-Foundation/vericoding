-- <vc-preamble>
def List.sum : List Int → Int 
  | [] => 0
  | x::xs => x + List.sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cal_points (ops : List String) : Int := sorry

theorem cal_points_basic_two_numbers :
  cal_points ["5", "2"] = 7 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cal_points_basic_double :
  cal_points ["1", "D"] = 3 := sorry

theorem cal_points_basic_plus :
  cal_points ["1", "2", "+"] = 6 := sorry

/-
info: 30
-/
-- #guard_msgs in
-- #eval cal_points ["5", "2", "C", "D", "+"]

/-
info: 27
-/
-- #guard_msgs in
-- #eval cal_points ["5", "-2", "4", "C", "D", "9", "+", "+"]

/-
info: 12
-/
-- #guard_msgs in
-- #eval cal_points ["1", "2", "+", "D"]
-- </vc-theorems>