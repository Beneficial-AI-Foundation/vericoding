-- <vc-preamble>
def power (x y : Nat) : Nat :=
  sorry

def order (x : Nat) : Nat :=
  sorry

def is_armstrong (x : Nat) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_numbers (numbers : List Nat) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem power_properties (x : Nat) (y : Nat) :
  (y = 0 → power x y = 1) ∧
  (y = 1 → power x y = x) ∧
  (y = 2 → power x y = x * x) :=
  sorry

theorem order_properties (x : Nat) :
  (x = 0 → order x = 0) ∧
  (0 < x ∧ x < 10 → order x = 1) ∧
  (10 ≤ x ∧ x < 100 → order x = 2) :=
  sorry

theorem is_armstrong_properties (x : Nat) :
  (x < 10 → is_armstrong x = "FEELS GOOD") ∧
  (is_armstrong x = "FEELS GOOD" ∨ is_armstrong x = "FEELS BAD") :=
  sorry

theorem check_numbers_properties (numbers : List Nat) :
  (numbers = [] → check_numbers numbers = []) ∧
  (List.length (check_numbers numbers) = List.length numbers) ∧
  (∀ x ∈ check_numbers numbers, x = "FEELS GOOD" ∨ x = "FEELS BAD") :=
  sorry

/-
info: ['FEELS GOOD', 'FEELS BAD', 'FEELS GOOD']
-/
-- #guard_msgs in
-- #eval check_numbers [153, 11, 1634]

/-
info: ['FEELS GOOD', 'FEELS GOOD', 'FEELS GOOD']
-/
-- #guard_msgs in
-- #eval check_numbers [370, 371, 407]

/-
info: ['FEELS BAD', 'FEELS BAD', 'FEELS BAD']
-/
-- #guard_msgs in
-- #eval check_numbers [123, 555, 999]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded