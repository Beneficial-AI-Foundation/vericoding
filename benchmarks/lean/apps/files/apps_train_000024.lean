-- <vc-helpers>
-- </vc-helpers>

def intToFloat : Int → Float := sorry

def solve_equation (d : Int) : Bool × Float × Float := sorry

theorem large_inputs_succeed (d : Int) : d ≥ 5 → d ≤ 1000 → (solve_equation d).1 = true := sorry

theorem non_positive_inputs_succeed (d : Int) : d ≤ 0 → d ≥ -1000 → (solve_equation d).1 = true := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible