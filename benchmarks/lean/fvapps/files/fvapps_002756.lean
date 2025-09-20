-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cost_of_carpet (length width roll_width roll_cost : Float) : Float := sorry

theorem cost_of_carpet_symmetry 
  (roll_width : Float) 
  (roll_cost : Float)
  (h1 : roll_width > 0.1 ∧ roll_width ≤ 100)
  (h2 : roll_cost > 0.01 ∧ roll_cost ≤ 100)
  : let length := roll_width / 2
    let width := roll_width / 3
    cost_of_carpet length width roll_width roll_cost = 
    cost_of_carpet width length roll_width roll_cost := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>