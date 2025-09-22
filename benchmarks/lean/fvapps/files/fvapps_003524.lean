-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Point := Float × Float

def get_slope : Point → Point → Option Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem slope_same_direction {p1 p2 : Point} :
  get_slope p1 p2 = get_slope p2 p1 := sorry

theorem slope_formula {p1 p2 : Point} (h : p1.1 ≠ p2.1) :
  match get_slope p1 p2 with
  | some s => (s - (p2.2 - p1.2)/(p2.1 - p1.1)).abs < 1e-10
  | none => False := sorry

theorem slope_same_point {p : Point} :
  get_slope p p = none := sorry

theorem slope_vertical {p1 p2 : Point} :
  p1.1 = p2.1 → get_slope p1 p2 = none := sorry
-- </vc-theorems>