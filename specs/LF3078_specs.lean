-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def guess_hat_color : Color → Color → Color → Color → Nat :=
  fun _ _ _ _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem guess_hat_result_valid {a b c d : Color} :
  (guess_hat_color a b c d = 1) ∨ (guess_hat_color a b c d = 2) := 
  sorry

theorem guess_hat_equal_gives_one {a b c d : Color} :
  (guess_hat_color a b c d = 1) = (b = c) :=
  sorry 

theorem guess_hat_unequal_gives_two {a b c d : Color} :
  (guess_hat_color a b c d = 2) = (b ≠ c) :=
  sorry

theorem guess_hat_preserves_colors (a b c d : Color) :
  (a = Color.black ∨ a = Color.white) ∧
  (b = Color.black ∨ b = Color.white) ∧
  (c = Color.black ∨ c = Color.white) ∧
  (d = Color.black ∨ d = Color.white) :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval guess_hat_color "white" "black" "white" "black"

/-
info: 1
-/
-- #guard_msgs in
-- #eval guess_hat_color "white" "black" "black" "white"
-- </vc-theorems>