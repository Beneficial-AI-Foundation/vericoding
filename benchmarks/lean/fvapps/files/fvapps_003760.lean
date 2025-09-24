-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def house_of_cards (n : Int) : Int := sorry

-- Results should be positive integers and greater than 7n
-- </vc-definitions>

-- <vc-theorems>
theorem house_of_cards_positive_integers {n : Int} (h : n > 0) : 
  house_of_cards n ≥ 7 * n ∧ house_of_cards n > 0 := sorry

-- Function should fail for non-positive inputs

theorem house_of_cards_invalid_inputs {n : Int} (h : n ≤ 0) :
  ¬ ∃ m, house_of_cards n = m := sorry 

-- Results should be strictly increasing

theorem house_of_cards_increasing {n : Int} (h : n > 1) :
  house_of_cards n > house_of_cards (n-1) := sorry

-- Each floor adds more cards than the previous floor

theorem house_of_cards_acceleration {n₁ n₂ n₃ : Int} 
  (h₁ : 0 < n₁) (h₂ : n₁ < n₂) (h₃ : n₂ < n₃) :
  house_of_cards n₂ - house_of_cards n₁ < 
  house_of_cards n₃ - house_of_cards n₂ := sorry
-- </vc-theorems>