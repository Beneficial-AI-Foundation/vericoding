-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def on_line (pts : List (Int × Int)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_single_point_collinear (pts : List (Int × Int)) :
  pts.length ≤ 1 → on_line pts = true :=
  sorry

theorem duplicate_points_preserves_collinearity (pts : List (Int × Int)) :
  pts.length > 0 → on_line (pts ++ pts) = on_line pts :=
  sorry

theorem vertical_line_collinear (x y1 y2 : Int) :
  let pts := [(x,y1), (x,y2)]
  let pts' := if y1 = y2 then pts else (x, (y1+y2)/2)::pts
  on_line pts' = true :=
  sorry

theorem horizontal_line_collinear (y x1 x2 : Int) :
  let pts := [(x1,y), (x2,y)]
  let pts' := if x1 = x2 then pts else ((x1+x2)/2,y)::pts
  on_line pts' = true :=
  sorry

theorem diagonal_line_collinear (start step1 step2 : Int) :
  let pts := [(start,start), (start+step1,start+step1), (start+step2,start+step2)]
  on_line pts = true :=
  sorry
-- </vc-theorems>