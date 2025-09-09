def next_happy_year (year : Nat) : Nat := sorry

-- Helper functions

-- <vc-helpers>
-- </vc-helpers>

def number_to_digits (n : Nat) : List Nat := sorry 
def count_unique (l : List Nat) : Nat := sorry

theorem next_happy_year_increases (year : Nat) 
  (h : year ≥ 1000 ∧ year ≤ 8999) :
  next_happy_year year > year := sorry

/-
info: 1023
-/
-- #guard_msgs in
-- #eval next_happy_year 1001

/-
info: 7801
-/
-- #guard_msgs in
-- #eval next_happy_year 7712

/-
info: 9012
-/
-- #guard_msgs in
-- #eval next_happy_year 8999

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible