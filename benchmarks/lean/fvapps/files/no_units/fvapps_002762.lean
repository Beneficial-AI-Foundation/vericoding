-- <vc-preamble>
def opposite (x : Int) : Int := sorry

theorem double_negative_int (x : Int) :
  opposite (opposite x) = x := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def opposite_real (x : Float) : Float := sorry 

theorem double_negative_real (x : Float) :
  opposite_real (opposite_real x) = x := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_is_self_opposite :
  opposite 0 = 0 := sorry

theorem nonzero_not_self_opposite (x : Int) :
  x ≠ 0 → opposite x ≠ x := sorry

theorem sum_with_opposite_int (x : Int) :
  x + opposite x = 0 := sorry
-- </vc-theorems>