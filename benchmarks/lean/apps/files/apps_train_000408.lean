-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def integer_replacement (n : Nat) : Nat := sorry

theorem integer_replacement_terminates (n : Nat) (h : n > 0) :
  integer_replacement n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem integer_replacement_is_nat (n : Nat) (h : n > 0) :
  integer_replacement n = integer_replacement n := sorry

theorem integer_replacement_base_case_one :
  integer_replacement 1 = 0 := sorry

theorem integer_replacement_base_case_two :
  integer_replacement 2 = 1 := sorry

theorem integer_replacement_power_of_two (n : Nat) (h : n > 0) :
  integer_replacement (2^n) = n := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval integer_replacement 8

/-
info: 4
-/
-- #guard_msgs in
-- #eval integer_replacement 7

/-
info: 2
-/
-- #guard_msgs in
-- #eval integer_replacement 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible