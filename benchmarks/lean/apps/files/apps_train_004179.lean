-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_sixes (n : Nat) : Nat := sorry

theorem count_sixes_non_negative (n : Nat) (h : n > 0) :
  count_sixes n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_sixes_monotonic (n : Nat) (h : n > 1) :
  count_sixes n ≥ count_sixes (n-1) := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_sixes 10

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_sixes 2

/-
info: 30
-/
-- #guard_msgs in
-- #eval count_sixes 100
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible