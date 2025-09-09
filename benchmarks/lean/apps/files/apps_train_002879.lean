-- <vc-helpers>
-- </vc-helpers>

def factorial : Int → Option Int
  | n => sorry

-- Basic factorial properties

theorem factorial_negative {n : Int} : 
  n < 0 → factorial n = none := sorry

theorem factorial_zero : 
  factorial 0 = some 1 := sorry

theorem factorial_multiplicative {n : Int} : 
  n > 0 → factorial n = some (n * (factorial (n-1)).get!) := sorry

theorem factorial_positive {n : Int} :
  n ≥ 0 → (factorial n).isSome ∧ (factorial n).get! > 0 := sorry

-- Recurrence relation

theorem factorial_recurrence {n : Int} :
  n > 0 → factorial n = some (n * (factorial (n-1)).get!) := sorry

-- Monotonicity

theorem factorial_increasing {n : Int} :
  n > 1 → (factorial n).get! > (factorial (n-1)).get! := sorry

/-
info: 120
-/
-- #guard_msgs in
-- #eval factorial 5

/-
info: 1
-/
-- #guard_msgs in
-- #eval factorial 0

/-
info: None
-/
-- #guard_msgs in
-- #eval factorial -5

-- Apps difficulty: introductory
-- Assurance level: unguarded