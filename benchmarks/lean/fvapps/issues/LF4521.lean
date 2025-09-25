-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_right_triangle (known : List (String × Float)) : RightTriangle := sorry

def is_valid_right_triangle (t : RightTriangle) : Bool := 
  let diff := t.a^2 + t.b^2 - t.c^2
  diff.abs < 0.0001
-- </vc-definitions>

-- <vc-theorems>
theorem solve_with_two_legs {a b : Float} (ha : a > 0.1) (hb : b > 0.1) 
  (ha_upper : a < 1000) (hb_upper : b < 1000) :
  let t := solve_right_triangle [("a", a), ("b", b)]
  is_valid_right_triangle t := sorry

theorem solve_with_leg_and_hyp_a {leg hyp : Float} (hl : leg > 0.1) (hh : hyp > 0.1)
  (hl_upper : leg < 1000) (hh_upper : hyp < 1000) (h_shorter : leg < hyp) :
  let t := solve_right_triangle [("a", leg), ("c", hyp)]
  is_valid_right_triangle t := sorry

theorem solve_with_leg_and_hyp_b {leg hyp : Float} (hl : leg > 0.1) (hh : hyp > 0.1) 
  (hl_upper : leg < 1000) (hh_upper : hyp < 1000) (h_shorter : leg < hyp) :
  let t := solve_right_triangle [("b", leg), ("c", hyp)]
  is_valid_right_triangle t := sorry

theorem invalid_inputs_empty :
  ∀ t, solve_right_triangle [] ≠ t := sorry

theorem invalid_inputs_bad_key :
  ∀ t, solve_right_triangle [("x", 3), ("y", 4)] ≠ t := sorry
-- </vc-theorems>