-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (x : Float) : Float := if x < 0 then -x else x

def close_compare (a b : Float) (margin : Float := 0) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem close_compare_valid_output (a b margin : Float) :
  let result := close_compare a b margin
  result = -1 ∨ result = 0 ∨ result = 1 := sorry

theorem close_compare_margin (a b margin : Float) :
  (abs (a - b) ≤ margin → close_compare a b margin = 0) ∧
  (b > a → close_compare a b margin = -1) ∧
  (b < a → close_compare a b margin = 1) := sorry

theorem close_compare_identical (x : Float) :
  close_compare x x = 0 ∧
  close_compare x x 1 = 0 := sorry

theorem close_compare_symmetry (a b : Float) :
  close_compare a b = -(close_compare b a) := sorry
-- </vc-theorems>