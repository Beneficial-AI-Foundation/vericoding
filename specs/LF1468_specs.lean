-- <vc-preamble>
def List.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + List.sum xs

def List.maximum' : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: xs => max x (List.maximum' xs)

/- Main function -/
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_max_earnings (n : Nat) (fees : List Nat) : Nat :=
  sorry

/- Theorems -/
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_max_earnings_bounded (n : Nat) (fees : List Nat) :
  n > 0 → fees.length = n → calculate_max_earnings n fees ≤ fees.sum :=
  sorry

theorem calculate_max_earnings_nonnegative (n : Nat) (fees : List Nat) :
  n > 0 → fees.length = n → calculate_max_earnings n fees ≥ 0 :=
  sorry

theorem calculate_max_earnings_returns_number (n : Nat) (fees : List Nat) :
  n > 0 → fees.length = n → calculate_max_earnings n fees = calculate_max_earnings n fees :=
  sorry

/-
info: 23
-/
-- #guard_msgs in
-- #eval calculate_max_earnings 5 [10, 3, 5, 7, 3]

/-
info: 17
-/
-- #guard_msgs in
-- #eval calculate_max_earnings 8 [3, 2, 3, 2, 3, 5, 1, 3]

/-
info: 6
-/
-- #guard_msgs in
-- #eval calculate_max_earnings 3 [1, 2, 3]
-- </vc-theorems>