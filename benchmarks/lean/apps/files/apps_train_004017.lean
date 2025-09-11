-- <vc-preamble>
def sum (f: Nat → Nat) (n: Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def squares_needed (n: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem squares_needed_zero :
  squares_needed 0 = 0 :=
  sorry

theorem squares_needed_one :
  squares_needed 1 = 1 :=
  sorry

theorem squares_needed_power_two :
  squares_needed (2^10) = 11 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval squares_needed 0

/-
info: 1
-/
-- #guard_msgs in
-- #eval squares_needed 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval squares_needed 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval squares_needed 3

/-
info: 3
-/
-- #guard_msgs in
-- #eval squares_needed 4
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible