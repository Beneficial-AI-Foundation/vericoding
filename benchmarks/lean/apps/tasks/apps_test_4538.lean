-- <vc-preamble>
def ValidInput (N D : Int) (points : List (Int × Int)) : Prop :=
  N ≥ 0 ∧ D ≥ 0 ∧ points.length ≥ N.natAbs

def WithinDistance (point : Int × Int) (D : Int) : Bool :=
  point.1 * point.1 + point.2 * point.2 ≤ D * D

def CountPointsWithinDistance (N D : Int) (points : List (Int × Int)) : Int :=
  if N ≤ 0 then 0 else
  (List.range N.natAbs).filter (fun i => 
    if h : i < points.length then WithinDistance points[i] D else false) |>.length

@[reducible, simp]
def solve_precond (N D : Int) (points : List (Int × Int)) : Prop :=
  ValidInput N D points
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N D : Int) (points : List (Int × Int)) (h_precond : solve_precond N D points) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N D : Int) (points : List (Int × Int)) (result : Int) (h_precond : solve_precond N D points) : Prop :=
  0 ≤ result ∧ result ≤ N ∧ result = CountPointsWithinDistance N D points

theorem solve_spec_satisfied (N D : Int) (points : List (Int × Int)) (h_precond : solve_precond N D points) :
    solve_postcond N D points (solve N D points h_precond) h_precond := by
  sorry
-- </vc-theorems>