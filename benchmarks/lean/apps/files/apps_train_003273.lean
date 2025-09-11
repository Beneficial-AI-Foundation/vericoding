-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def f (x : α) : Option Nat := sorry

/- For positive integers, f(n) equals the sum of numbers from 1 to n -/
-- </vc-definitions>

-- <vc-theorems>
theorem positive_integers_sum {n : Nat} (h : n > 0) : 
  f n = some (n * (n + 1) / 2) := sorry

/- For non-positive integers, f returns none -/

theorem non_positive_returns_none {n : Int} (h : n ≤ 0) :
  f n = none := sorry

/- For non-integer numeric inputs, f returns none -/  

theorem non_integer_returns_none (x : Float) :
  f x = none := sorry

/- For any non-numeric type α, f returns none -/

theorem non_numeric_returns_none (α : Type) (x : α) :
  f x = none := sorry

/- f handles large inputs without overflow -/

theorem handles_large_inputs (n : Nat) :
  f n ≠ none → ∃ m : Nat, f n = some m ∧ m > 0 := sorry

/-
info: 5050
-/
-- #guard_msgs in
-- #eval f 100

/-
info: None
-/
-- #guard_msgs in
-- #eval f 0

/-
info: None
-/
-- #guard_msgs in
-- #eval f 3.14
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded