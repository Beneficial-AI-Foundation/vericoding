-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numberOfRoutes (m n : Nat) : Nat := sorry

theorem numberOfRoutes_positive (m n : Nat) (h1: m > 0) (h2: n > 0) : 
  numberOfRoutes m n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numberOfRoutes_symmetric (m n : Nat) :
  numberOfRoutes m n = numberOfRoutes n m := sorry

theorem numberOfRoutes_single_row (n : Nat) (h: n > 0) :
  numberOfRoutes 1 n = n + 1 := sorry

theorem numberOfRoutes_single_col (n : Nat) (h: n > 0) :
  numberOfRoutes n 1 = n + 1 := sorry

theorem numberOfRoutes_minimal :
  numberOfRoutes 1 1 = 2 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval number_of_routes 1 1

/-
info: 35
-/
-- #guard_msgs in
-- #eval number_of_routes 3 4

/-
info: 462
-/
-- #guard_msgs in
-- #eval number_of_routes 5 6
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded