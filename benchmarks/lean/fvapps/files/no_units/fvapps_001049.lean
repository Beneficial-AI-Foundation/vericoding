-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>