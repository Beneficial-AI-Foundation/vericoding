-- <vc-helpers>
-- </vc-helpers>

def bowling_score (rolls : List Nat) : Nat := sorry

theorem score_bounds (rolls : List Nat) (validRolls : True) :
  let score := bowling_score rolls
  0 ≤ score ∧ score ≤ 300 := sorry

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

/-
info: 0
-/
-- #guard_msgs in
-- #eval bowling_score [0] * 20

/-
info: 20
-/
-- #guard_msgs in
-- #eval bowling_score [1] * 20

/-
info: 300
-/
-- #guard_msgs in
-- #eval bowling_score [10] * 12

-- Apps difficulty: introductory
-- Assurance level: unguarded