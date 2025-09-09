-- <vc-helpers>
-- </vc-helpers>

def tribonacci (n : Int) : Int :=
  sorry

theorem tribonacci_base_zero :
  tribonacci 0 = 0 :=
  sorry

theorem tribonacci_base_one :
  tribonacci 1 = 1 :=
  sorry

theorem tribonacci_base_two :
  tribonacci 2 = 1 :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval tribonacci 4

/-
info: 1389537
-/
-- #guard_msgs in
-- #eval tribonacci 25

/-
info: 0
-/
-- #guard_msgs in
-- #eval tribonacci 0

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible