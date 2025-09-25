-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def weighBalls (scales : MockScales) (left right : List Nat) : Weigh := sorry

def find_ball (scales : MockScales) (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_ball_correct 
  (n : Nat)
  (heavy_idx : Nat)
  (h₁ : 0 < n)
  (h₂ : heavy_idx < n) :
  find_ball (MockScales.mk heavy_idx) n = heavy_idx := sorry

theorem find_ball_complexity
  (n : Nat)
  (heavy_idx : Nat)
  (h₁ : 0 < n) 
  (h₂ : heavy_idx < n) :
  ∃ uses : Nat, uses ≤ max 1 (Nat.log2 n) := sorry

theorem find_ball_edge_cases
  (n : Nat)
  (h : 0 < n) :
  find_ball (MockScales.mk 0) n = 0 ∧ 
  find_ball (MockScales.mk (n-1)) n = n-1 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_ball MockScales(3) 8

/-
info: 15
-/
-- #guard_msgs in
-- #eval find_ball MockScales(15) 27

/-
info: 80
-/
-- #guard_msgs in
-- #eval find_ball MockScales(80) 81
-- </vc-theorems>