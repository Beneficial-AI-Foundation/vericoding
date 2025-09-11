-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_cinema_seating (n m z l r b : Nat) : Nat :=
  sorry

-- Main properties theorem
-- </vc-definitions>

-- <vc-theorems>
theorem cinema_seating_basic_properties 
  (n m z l r b : Nat) :
  let result := solve_cinema_seating n m z l r b;
  let total_seats := n * m;
  let min_seats := min (n * m) (l + r);
  result ≤ total_seats 
  ∧ result ≥ min_seats
  ∧ result ≥ 0 :=
  sorry

-- Symmetry property

theorem cinema_seating_symmetry
  (n m z l r b : Nat) :
  solve_cinema_seating n m z l r b = solve_cinema_seating n m z r l b :=
  sorry

-- Zero case property  

theorem cinema_seating_zero_case
  (n m : Nat) :
  n > 0 → m > 0 → solve_cinema_seating n m 0 0 0 0 = 0 :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_cinema_seating 2 2 3 2 1 1

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_cinema_seating 3 3 1 2 0 9

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_cinema_seating 1 2 1 1 1 0
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded