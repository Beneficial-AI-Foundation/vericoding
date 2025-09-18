-- <vc-preamble>
def isDigit (c : Char) : Bool := sorry

def isBouncyStr (s : String) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bouncyRatio (n : Float) : Float := sorry

theorem bouncy_sequence_property {n : Nat} (h : n ≥ 100) (h2 : n ≤ 100000) :
  isBouncyStr (toString n) = true →
  ∃ i j : String.Pos, i < j ∧ 
  ((toString n).get i < (toString n).get j) ∧
  ∃ k l : String.Pos, k < l ∧
  ((toString n).get k > (toString n).get l) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bouncy_ratio_validation_zero :
  ¬ ∃ x : Float, x = bouncyRatio 0 := sorry

theorem bouncy_ratio_validation_one :
  ¬ ∃ x : Float, x = bouncyRatio 1 := sorry

theorem bouncy_ratio_validation_negative (n : Float) :
  n < 0 →
  ¬ ∃ x : Float, x = bouncyRatio n := sorry

theorem bouncy_ratio_validation_above_one (n : Float) :
  n > 1 →
  ¬ ∃ x : Float, x = bouncyRatio n := sorry

/-
info: 538
-/
-- #guard_msgs in
-- #eval bouncy_ratio 0.5

/-
info: 21780
-/
-- #guard_msgs in
-- #eval bouncy_ratio 0.9

/-
info: 3088
-/
-- #guard_msgs in
-- #eval bouncy_ratio 0.75
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded