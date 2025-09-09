def difference_of_squares (n : Nat) : Nat :=
  sorry

def sum_up_to (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def sum_squares_up_to (n : Nat) : Nat :=
  sorry

theorem difference_non_negative {n : Nat} : 
  difference_of_squares n ≥ 0 := 
  sorry

theorem zero_and_one_cases :
  difference_of_squares 0 = 0 ∧ difference_of_squares 1 = 0 :=
  sorry

theorem strictly_increasing {n : Nat} (h : n ≥ 2) :
  difference_of_squares n > difference_of_squares (n-1) :=
  sorry

/-
info: 170
-/
-- #guard_msgs in
-- #eval difference_of_squares 5

/-
info: 2640
-/
-- #guard_msgs in
-- #eval difference_of_squares 10

/-
info: 25164150
-/
-- #guard_msgs in
-- #eval difference_of_squares 100

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible