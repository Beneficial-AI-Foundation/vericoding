-- <vc-helpers>
-- </vc-helpers>

def isLastDigitPretty (n : Nat) : Bool := sorry

def count_pretty_numbers (l r : Nat) : Nat := sorry

theorem count_pretty_numbers_non_negative (l r : Nat) : 
  count_pretty_numbers l r ≥ 0 := sorry

theorem count_pretty_numbers_bounded (l r : Nat) :
  count_pretty_numbers l r ≤ (max l r - min l r + 1) := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_pretty_numbers 1 10

/-
info: 8
-/
-- #guard_msgs in
-- #eval count_pretty_numbers 11 33

/-
info: 30
-/
-- #guard_msgs in
-- #eval count_pretty_numbers 1 100

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible