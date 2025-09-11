-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def padovan (n : Nat) : Nat := sorry

theorem padovan_positive (n : Nat) : 
  padovan n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem padovan_first_three : 
  (padovan 0 = 1) ∧ (padovan 1 = 1) ∧ (padovan 2 = 1) := sorry

theorem padovan_recurrence (n : Nat) :
  padovan (n + 3) = padovan n + padovan (n + 1) := sorry

theorem padovan_monotonic (n : Nat) :
  n > 0 → padovan n ≥ padovan (n - 1) := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval padovan 0

/-
info: 1
-/
-- #guard_msgs in
-- #eval padovan 1

/-
info: 1
-/
-- #guard_msgs in
-- #eval padovan 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval padovan 3

/-
info: 2
-/
-- #guard_msgs in
-- #eval padovan 4

/-
info: 12
-/
-- #guard_msgs in
-- #eval padovan 10

/-
info: 1177482265857
-/
-- #guard_msgs in
-- #eval padovan 100
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible