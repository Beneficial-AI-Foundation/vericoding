-- <vc-preamble>
def Coordinates := (Nat × Nat × Nat × Nat)
def SearchPlan := (Nat × List Coordinates)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_police_search_plan : SearchPlan :=
sorry

-- Output format theorem
-- </vc-definitions>

-- <vc-theorems>
theorem search_plan_output_format (plan : SearchPlan) : 
  let (N, coords) := plan
  ∀ c ∈ coords, ∃ x1 y1 x2 y2 : Nat, c = (x1, y1, x2, y2) :=
sorry

-- Length consistency theorem

theorem search_plan_length_consistency (plan : SearchPlan) :
  let (N, coords) := plan
  List.length coords = N ∧
  N ≤ 2015 :=
sorry

-- Coordinate bounds theorem

theorem search_plan_coordinate_bounds (plan : SearchPlan) :
  let (N, coords) := plan
  ∀ c ∈ coords,
    let (x1, y1, x2, y2) := c
    1 ≤ x1 ∧ x1 ≤ 1000 ∧
    1 ≤ y1 ∧ y1 ≤ 2 ∧
    1 ≤ x2 ∧ x2 ≤ 1000 ∧
    1 ≤ y2 ∧ y2 ≤ 2 :=
sorry

-- Search plan validity theorem

theorem search_plan_validity (coords : List Coordinates) (h : coords.length ≥ 1) :
  ∀ c ∈ coords,
    let (x1, y1, x2, y2) := c
    1 ≤ x1 ∧ x1 ≤ 1000 ∧
    1 ≤ y1 ∧ y1 ≤ 2 ∧ 
    1 ≤ x2 ∧ x2 ≤ 1000 ∧
    1 ≤ y2 ∧ y2 ≤ 2 :=
sorry
-- </vc-theorems>