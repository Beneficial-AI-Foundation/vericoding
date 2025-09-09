-- <vc-helpers>
-- </vc-helpers>

def max_satisfaction (satisfaction : List Int) : Int :=
  sorry

theorem max_satisfaction_nonnegative
  (satisfaction : List Int) :
  max_satisfaction satisfaction ≥ 0 :=
  sorry

theorem max_satisfaction_empty :
  max_satisfaction [] = 0 :=
  sorry

theorem max_satisfaction_single_zero :
  max_satisfaction [0] = 0 :=
  sorry

theorem max_satisfaction_single_positive :
  max_satisfaction [1] = 1 :=
  sorry

theorem max_satisfaction_single_negative :
  max_satisfaction [-1] = 0 :=
  sorry

/-
info: 14
-/
-- #guard_msgs in
-- #eval max_satisfaction [-1, -8, 0, 5, -9]

/-
info: 20
-/
-- #guard_msgs in
-- #eval max_satisfaction [4, 3, 2]

/-
info: 35
-/
-- #guard_msgs in
-- #eval max_satisfaction [-2, 5, -1, 0, 3, -3]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible