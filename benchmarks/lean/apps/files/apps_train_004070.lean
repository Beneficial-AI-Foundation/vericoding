-- <vc-helpers>
-- </vc-helpers>

def calculate_1RM (weight : Int) (reps : Int) : Int := sorry

-- Non-negative result

theorem rm_nonnegative (weight reps : Int) 
  (hw : weight ≥ 0) (hr : reps ≥ 0) :
  calculate_1RM weight reps ≥ 0 := sorry

-- Zero reps gives zero result  

theorem rm_zero_reps (weight : Int) 
  (hw : weight ≥ 0) :
  calculate_1RM weight 0 = 0 := sorry

-- One rep equals weight

theorem rm_one_rep (weight : Int)
  (hw : weight ≥ 0) :
  calculate_1RM weight 1 = weight := sorry

-- Result >= weight for multiple reps

theorem rm_ge_weight (weight reps : Int)
  (hw : weight ≥ 0) (hr : reps > 1) :
  calculate_1RM weight reps ≥ weight := sorry

-- Result is integer 

theorem rm_is_int (weight reps : Int)
  (hw : weight ≥ 0) (hr : reps ≥ 0) :
  calculate_1RM weight reps = (calculate_1RM weight reps) := sorry

/-
info: 282
-/
-- #guard_msgs in
-- #eval calculate_1RM 135 20

/-
info: 253
-/
-- #guard_msgs in
-- #eval calculate_1RM 200 8

/-
info: 289
-/
-- #guard_msgs in
-- #eval calculate_1RM 270 2

/-
info: 360
-/
-- #guard_msgs in
-- #eval calculate_1RM 360 1

/-
info: 0
-/
-- #guard_msgs in
-- #eval calculate_1RM 400 0

-- Apps difficulty: introductory
-- Assurance level: guarded