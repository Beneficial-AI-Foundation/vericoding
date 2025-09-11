-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_sum_two_no_overlap (A : List Int) (L M : Nat) : Int := sorry

theorem equal_window_sizes (A : List Int) (L : Nat) :
  2 * L ≤ A.length →
  max_sum_two_no_overlap A L L = max_sum_two_no_overlap A L L := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_sum_two_bounds (A : List Int) (L M : Nat) :
  -- Result is symmetric for L and M
  max_sum_two_no_overlap A L M = max_sum_two_no_overlap A M L := by sorry

/-
info: 20
-/
-- #guard_msgs in
-- #eval max_sum_two_no_overlap [0, 6, 5, 2, 2, 5, 1, 9, 4] 1 2

/-
info: 29
-/
-- #guard_msgs in
-- #eval max_sum_two_no_overlap [3, 8, 1, 3, 2, 1, 8, 9, 0] 3 2

/-
info: 31
-/
-- #guard_msgs in
-- #eval max_sum_two_no_overlap [2, 1, 5, 6, 0, 9, 5, 0, 3, 8] 4 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded