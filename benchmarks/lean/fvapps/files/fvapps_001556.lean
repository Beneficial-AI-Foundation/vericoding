-- <vc-preamble>
def who_is_winner (moves : List String) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def columnHeight (moves : List String) (col : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_result_states (moves : List String) :
  let result := who_is_winner moves
  result = "Red" ∨ result = "Yellow" ∨ result = "Draw" := by
  sorry

theorem column_height_bound (moves : List String) (col : String) :
  columnHeight moves col ≤ 6 := by
  sorry

/-
info: 'Yellow'
-/
-- #guard_msgs in
-- #eval who_is_winner ["A_Red", "B_Yellow", "A_Red", "B_Yellow", "A_Red", "B_Yellow", "G_Red", "B_Yellow"]

/-
info: 'Red'
-/
-- #guard_msgs in
-- #eval who_is_winner ["A_Yellow", "B_Red", "B_Yellow", "C_Red", "G_Yellow", "C_Red", "C_Yellow", "D_Red", "G_Yellow", "D_Red", "G_Yellow", "D_Red", "F_Yellow", "E_Red", "D_Yellow"]

/-
info: 'Yellow'
-/
-- #guard_msgs in
-- #eval who_is_winner ["C_Yellow", "E_Red", "G_Yellow", "B_Red", "D_Yellow", "B_Red", "B_Yellow", "G_Red", "C_Yellow", "C_Red", "D_Yellow", "F_Red", "E_Yellow", "A_Red", "A_Yellow", "G_Red", "A_Yellow", "F_Red", "F_Yellow", "D_Red", "B_Yellow", "E_Red", "D_Yellow", "A_Red", "G_Yellow", "D_Red", "D_Yellow", "C_Red"]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded