-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate (s : String) : Option Int := sorry

@[simp] theorem calculate_positive_number (n : Int) 
  (h : 1 ≤ n ∧ n ≤ 100) : 
  calculate (toString n) = some n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_addition (a b : Int)
  (h₁ : 1 ≤ a ∧ a ≤ 50) (h₂ : 1 ≤ b ∧ b ≤ 50) :
  calculate (toString a ++ "+" ++ toString b) = some (a + b) := sorry

theorem calculate_multiplication (a b : Int)
  (h₁ : 1 ≤ a ∧ a ≤ 50) (h₂ : 1 ≤ b ∧ b ≤ 50) :
  calculate (toString a ++ "*" ++ toString b) = some (a * b) := sorry

theorem calculate_division (a b : Int)
  (h₁ : 1 ≤ a ∧ a ≤ 50) (h₂ : 1 ≤ b ∧ b ≤ 50) :
  calculate (toString a ++ "/" ++ toString b) = some (a / b) := sorry
-- </vc-theorems>