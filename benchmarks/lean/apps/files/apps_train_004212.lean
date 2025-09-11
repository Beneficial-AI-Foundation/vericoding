-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_ball (velocity : Float) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_ball_nonnegative (v : Float) :
  v > 0 → max_ball v ≥ 0 := 
  sorry

theorem max_ball_roughly_linear (v : Float) :
  v > 0 → (Float.ofInt (max_ball v) - v * 0.28) ≤ 1 ∧ 
          (Float.ofInt (max_ball v) - v * 0.28) ≥ -1 :=
  sorry

theorem max_ball_monotonic (v₁ v₂ : Float) :
  v₁ > v₂ → v₂ > 0 → max_ball v₁ ≥ max_ball v₂ :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval max_ball 15

/-
info: 7
-/
-- #guard_msgs in
-- #eval max_ball 25

/-
info: 10
-/
-- #guard_msgs in
-- #eval max_ball 37
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded