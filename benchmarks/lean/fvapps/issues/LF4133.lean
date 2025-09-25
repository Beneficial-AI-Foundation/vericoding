-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ellipse_contains_point (f0 : Point) (f1 : Point) (l : Float) (p : Point) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ellipse_contains_point_bool_result (f0 f1 : Point) (l : Float) (p : Point)
  (h : l > 0) : 
  (ellipse_contains_point f0 f1 l p = true ∨ ellipse_contains_point f0 f1 l p = false) :=
sorry

theorem coincident_foci_contains_focus (f0 : Point) (l : Float)
  (h : l > 0) :
  ellipse_contains_point f0 f0 l f0 = true :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval ellipse_contains_point {"x": 0, "y": 0} {"x": 0, "y": 0} 2 {"x": 0, "y": 0}

/-
info: False
-/
-- #guard_msgs in
-- #eval ellipse_contains_point f0 f1 l {"x": 1, "y": 1}

/-
info: True
-/
-- #guard_msgs in
-- #eval ellipse_contains_point {"x": -1, "y": 0} {"x": 1, "y": 0} 4 {"x": 0, "y": 1}
-- </vc-theorems>