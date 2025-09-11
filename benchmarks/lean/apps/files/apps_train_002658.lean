-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def group_size (s d: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem group_size_is_nat (s d: Nat) (h1: s > 0) (h2: s ≤ 100) (h3: d ≤ 1000) :
  group_size s d ≥ 0 := sorry

theorem group_size_known_cases : 
  (group_size 1 6 = 3) ∧ 
  (group_size 3 10 = 5) ∧ 
  (group_size 5 7 = 6) := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval group_size 1 6

/-
info: 5
-/
-- #guard_msgs in
-- #eval group_size 3 10

/-
info: 6
-/
-- #guard_msgs in
-- #eval group_size 5 7
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible