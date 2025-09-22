-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solution (x : Float) : Float :=
sorry

def floor (x : Float) : Float :=
sorry

def ceil (x : Float) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_output_options (x : Float) :
  let floorX := floor x
  solution x = floorX ∨ solution x = floorX + 0.5 ∨ solution x = ceil x
  :=
sorry

theorem solution_within_half (x : Float) :
  (solution x - x) ≤ 0.5 ∧ (x - solution x) ≤ 0.5
  :=
sorry

theorem solution_cases (x : Float) :
  let floorX := floor x
  (x - floorX < 0.25 → solution x = floorX) ∧
  (x - floorX < 0.75 ∧ x - floorX ≥ 0.25 → solution x = floorX + 0.5) ∧
  (x - floorX ≥ 0.75 → solution x = ceil x)
  :=
sorry
-- </vc-theorems>