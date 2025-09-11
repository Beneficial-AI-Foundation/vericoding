-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digits (n : Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem digits_positive (n : Nat) :
  digits n > 0 :=
sorry

theorem single_digit_numbers (n : Nat) (h : n > 0 ∧ n < 10) : 
  digits n = 1 :=
sorry 

theorem digits_equals_string_length (n : Int) :
  digits (Int.natAbs n) = String.length (toString (Int.natAbs n)) :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval digits 5

/-
info: 5
-/
-- #guard_msgs in
-- #eval digits 12345

/-
info: 10
-/
-- #guard_msgs in
-- #eval digits 9876543210
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible