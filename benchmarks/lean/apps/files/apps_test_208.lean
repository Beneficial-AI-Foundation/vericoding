-- <vc-preamble>
def ValidInput (x1 y1 x2 y2 : Int) : Prop :=
  -100 ≤ x1 ∧ x1 ≤ 100 ∧ -100 ≤ y1 ∧ y1 ≤ 100 ∧ -100 ≤ x2 ∧ x2 ≤ 100 ∧ -100 ≤ y2 ∧ y2 ≤ 100

def IsInvalidCase (x1 y1 x2 y2 : Int) : Prop :=
  x1 ≠ x2 ∧ y1 ≠ y2 ∧ Int.natAbs (x1 - x2) ≠ Int.natAbs (y1 - y2)

def IsDiagonalCase (x1 y1 x2 y2 : Int) : Prop :=
  x1 ≠ x2 ∧ y1 ≠ y2 ∧ Int.natAbs (x1 - x2) = Int.natAbs (y1 - y2)

def IsVerticalEdgeCase (x1 y1 x2 y2 : Int) : Prop :=
  x1 = x2

def IsHorizontalEdgeCase (x1 y1 x2 y2 : Int) : Prop :=
  x1 ≠ x2 ∧ y1 = y2

def ExpectedDiagonalResult (x1 y1 x2 y2 : Int) : List Int :=
  [x1, y2, x2, y1]

def ExpectedVerticalResult (x1 y1 x2 y2 : Int) : List Int :=
  [x1 + Int.natAbs (y2 - y1), y1, x1 + Int.natAbs (y2 - y1), y2]

def ExpectedHorizontalResult (x1 y1 x2 y2 : Int) : List Int :=
  [x1, y1 + Int.natAbs (x2 - x1), x2, y1 + Int.natAbs (x2 - x1)]

def ValidOutput (result : List Int) : Prop :=
  (result.length = 1 ∧ result.get! 0 = -1) ∨
  (result.length = 4 ∧ (∀ i, 0 ≤ i ∧ i < 4 → -1000 ≤ result.get! i ∧ result.get! i ≤ 1000))

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
  ValidOutput result ∧
  (IsInvalidCase x1 y1 x2 y2 → result = [-1]) ∧
  (IsDiagonalCase x1 y1 x2 y2 → result = ExpectedDiagonalResult x1 y1 x2 y2) ∧
  (IsVerticalEdgeCase x1 y1 x2 y2 → result = ExpectedVerticalResult x1 y1 x2 y2) ∧
  (IsHorizontalEdgeCase x1 y1 x2 y2 → result = ExpectedHorizontalResult x1 y1 x2 y2)

theorem solve_spec_satisfied (x1 y1 x2 y2 : Int) (h_precond : solve_precond x1 y1 x2 y2) :
    solve_postcond x1 y1 x2 y2 (solve x1 y1 x2 y2 h_precond) h_precond := by
  sorry
-- </vc-theorems>