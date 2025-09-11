-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tribonacci (n : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible