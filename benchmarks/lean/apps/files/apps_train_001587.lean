def sum_of_squares (n : Nat) : Nat := sorry
def one_square (n : Nat) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def two_squares (n : Nat) : Bool := sorry
def three_squares (n : Nat) : Bool := sorry

theorem sum_of_squares_range (n : Nat) (h : n ≥ 1) : 
  1 ≤ sum_of_squares n ∧ sum_of_squares n ≤ 4 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval sum_of_squares 15

/-
info: 1
-/
-- #guard_msgs in
-- #eval sum_of_squares 16

/-
info: 2
-/
-- #guard_msgs in
-- #eval sum_of_squares 17

/-
info: 1
-/
-- #guard_msgs in
-- #eval sum_of_squares 999887641

/-
info: 3
-/
-- #guard_msgs in
-- #eval sum_of_squares 999950886

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible