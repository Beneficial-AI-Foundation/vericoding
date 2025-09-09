-- <vc-helpers>
-- </vc-helpers>

def is_divisible (wallLength : Nat) (pixelSize : Nat) : Bool :=
  sorry

theorem is_divisible_correct {wallLength pixelSize : Nat} (h : pixelSize > 0) :
  is_divisible wallLength pixelSize = true ↔ wallLength % pixelSize = 0
  := sorry

theorem multiple_divisible {wallLength pixelSize : Nat} (h : pixelSize > 0) :
  is_divisible (wallLength * pixelSize) pixelSize = true
  := sorry

theorem zero_pixel_error (wallLength : Nat) :
  is_divisible wallLength 0 = false
  := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_divisible 4050 27

/-
info: False
-/
-- #guard_msgs in
-- #eval is_divisible 4066 27

/-
info: True
-/
-- #guard_msgs in
-- #eval is_divisible 10000 20

-- Apps difficulty: introductory
-- Assurance level: unguarded