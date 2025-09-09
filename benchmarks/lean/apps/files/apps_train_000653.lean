-- <vc-helpers>
-- </vc-helpers>

def String.toFloat? (s : String) : Option Float := sorry

def solve_geometry (x1 y1 x2 y2 : Int) (queries : List (Int × Int)) : List String :=
sorry

theorem solve_geometry_basic_properties {x1 y1 x2 y2 : Int} (h : x1 ≠ x2) 
  (queries : List (Int × Int)) :
  match solve_geometry x1 y1 x2 y2 queries with
  | result =>
    (result.length = queries.length ∨ result.length = 2 * queries.length) ∧
    ∀ i : Nat, i < result.length →
      if i % 2 = 0 
      then List.get! result i = "YES" ∨ List.get! result i = "NO"
      else ∃ d : Float, (List.get! result i).toFloat? = some d ∧ d ≥ 0 :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded