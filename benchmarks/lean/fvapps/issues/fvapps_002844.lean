-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def not_so_random (b w : Nat) : Color :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_valid (b w : Nat) :
  not_so_random b w = Color.Black ∨ not_so_random b w = Color.White :=
  sorry

theorem odd_black_returns_black (b w : Nat) :
  b % 2 = 1 → not_so_random b w = Color.Black :=
  sorry

theorem even_black_returns_white (b w : Nat) :
  b % 2 = 0 → not_so_random b w = Color.White :=
  sorry

theorem white_count_irrelevant (b w₁ w₂ : Nat) :
  not_so_random b w₁ = not_so_random b w₂ :=
  sorry

/-
info: 'Black'
-/
-- #guard_msgs in
-- #eval not_so_random 1 1

/-
info: 'White'
-/
-- #guard_msgs in
-- #eval not_so_random 2 1

/-
info: 'Black'
-/
-- #guard_msgs in
-- #eval not_so_random 11111 22222
-- </vc-theorems>