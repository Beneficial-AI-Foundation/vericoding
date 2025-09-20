-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def factorial : Int → Option Int
  | n => sorry

-- Basic factorial properties
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>