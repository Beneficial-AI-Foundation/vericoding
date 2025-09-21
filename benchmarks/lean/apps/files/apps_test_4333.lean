-- <vc-preamble>
def ValidInput (x1 y1 x2 y2 : Int) : Prop :=
  (x1, y1) ≠ (x2, y2) ∧
  -100 ≤ x1 ∧ x1 ≤ 100 ∧ -100 ≤ y1 ∧ y1 ≤ 100 ∧
  -100 ≤ x2 ∧ x2 ≤ 100 ∧ -100 ≤ y2 ∧ y2 ≤ 100

def ComputeThirdVertex (x1 y1 x2 y2 : Int) : (Int × Int) :=
  (x2 - (y2 - y1), y2 + (x2 - x1))

def ComputeFourthVertex (x1 y1 x2 y2 : Int) : (Int × Int) :=
  (x1 - (y2 - y1), y1 + (x2 - x1))

def ValidOutput (x1 y1 x2 y2 : Int) (result : List Int) : Prop :=
  result.length = 4 ∧
  result[0]! = (ComputeThirdVertex x1 y1 x2 y2).1 ∧
  result[1]! = (ComputeThirdVertex x1 y1 x2 y2).2 ∧
  result[2]! = (ComputeFourthVertex x1 y1 x2 y2).1 ∧
  result[3]! = (ComputeFourthVertex x1 y1 x2 y2).2

@[reducible, simp]
def solve_precond (x1 y1 x2 y2 : Int) : Prop :=
  ValidInput x1 y1 x2 y2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (x1 y1 x2 y2 : Int) (h_precond : solve_precond x1 y1 x2 y2) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x1 y1 x2 y2 : Int) (result : List Int) (h_precond : solve_precond x1 y1 x2 y2) : Prop :=
  ValidOutput x1 y1 x2 y2 result

theorem solve_spec_satisfied (x1 y1 x2 y2 : Int) (h_precond : solve_precond x1 y1 x2 y2) :
    solve_postcond x1 y1 x2 y2 (solve x1 y1 x2 y2 h_precond) h_precond := by
  sorry
-- </vc-theorems>