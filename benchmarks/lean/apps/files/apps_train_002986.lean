-- <vc-helpers>
-- </vc-helpers>

def is_happy (n : Nat) : Bool := sorry

def happy_numbers (n : Nat) : List Nat := sorry

theorem happy_numbers_consistent {n : Nat} (h : n > 0) :
  happy_numbers n = happy_numbers n := sorry

theorem happy_numbers_specific_values :
  1 ∈ happy_numbers 1 ∧
  1 ∈ happy_numbers 100 ∧
  7 ∈ happy_numbers 100 ∧
  10 ∈ happy_numbers 100 ∧
  13 ∈ happy_numbers 100 ∧
  19 ∈ happy_numbers 100 ∧
  4 ∉ happy_numbers 100 := sorry

/-
info: [1, 7, 10]
-/
-- #guard_msgs in
-- #eval happy_numbers 10

/-
info: [1, 7, 10, 13, 19, 23, 28, 31, 32, 44, 49]
-/
-- #guard_msgs in
-- #eval happy_numbers 50

/-
info: [1, 7, 10, 13, 19, 23, 28, 31, 32, 44, 49, 68, 70, 79, 82, 86, 91, 94, 97, 100]
-/
-- #guard_msgs in
-- #eval happy_numbers 100

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible