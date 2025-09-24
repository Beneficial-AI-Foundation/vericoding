-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_divisible (wallLength : Nat) (pixelSize : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_divisible_correct {wallLength pixelSize : Nat} (h : pixelSize > 0) :
  is_divisible wallLength pixelSize = true ↔ wallLength % pixelSize = 0
  := sorry

theorem multiple_divisible {wallLength pixelSize : Nat} (h : pixelSize > 0) :
  is_divisible (wallLength * pixelSize) pixelSize = true
  := sorry

theorem zero_pixel_error (wallLength : Nat) :
  is_divisible wallLength 0 = false
  := sorry
-- </vc-theorems>