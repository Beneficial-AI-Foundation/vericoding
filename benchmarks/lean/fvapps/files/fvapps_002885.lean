-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bowling_score (rolls : List Nat) : Nat := sorry

theorem score_bounds (rolls : List Nat) (validRolls : True) :
  let score := bowling_score rolls
  0 ≤ score ∧ score ≤ 300 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem frame_scores (rolls : List Nat) (validRolls : True) :
  ∀ (i : Nat) (h : i < rolls.length), 
    (rolls.get ⟨i, h⟩ = 10 → rolls.get ⟨i, h⟩ ≤ 10) ∧ 
    (rolls.get ⟨i, h⟩ ≠ 10 → 
     ∀ (h' : i + 1 < rolls.length), 
     rolls.get ⟨i, h⟩ + rolls.get ⟨i + 1, h'⟩ ≤ 10) := sorry

theorem all_zeros (rolls : List Nat) :
  rolls.length = 20 → 
  (∀ x ∈ rolls, x = 0) →
  bowling_score rolls = 0 := sorry

theorem perfect_game (rolls : List Nat) :
  rolls.length = 12 →
  (∀ x ∈ rolls, x = 10) →
  bowling_score rolls = 300 := sorry
-- </vc-theorems>