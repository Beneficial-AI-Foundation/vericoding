-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_snake_segments (x11 y11 x12 y12 x21 y21 x22 y22 : Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_snake_segments_returns_valid_result 
  (x11 y11 x12 y12 x21 y21 x22 y22 : Int) :
  check_snake_segments x11 y11 x12 y12 x21 y21 x22 y22 = "yes" ∨ 
  check_snake_segments x11 y11 x12 y12 x21 y21 x22 y22 = "no" :=
sorry

theorem check_snake_segments_reflexive
  (x1 y1 x2 y2 : Int) :
  check_snake_segments x1 y1 x2 y2 x1 y1 x2 y2 = "yes" :=
sorry

theorem check_snake_segments_symmetric
  (x1 y1 x2 y2 : Int) :
  check_snake_segments x1 y1 x2 y2 x2 y2 x1 y1 = 
  check_snake_segments x2 y2 x1 y1 x1 y1 x2 y2 :=
sorry

theorem check_snake_segments_horizontal_overlap
  (x y : Int) :
  check_snake_segments x y (x+5) y (x+3) y (x+8) y = "yes" :=
sorry

theorem check_snake_segments_vertical_overlap
  (x y : Int) :
  check_snake_segments x y x (y+5) x (y+3) x (y+8) = "yes" :=
sorry
-- </vc-theorems>