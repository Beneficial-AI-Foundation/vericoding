-- <vc-preamble>
def ValidInput (x y : Int) : Prop :=
  -100 ≤ x ∧ x ≤ 100 ∧ -100 ≤ y ∧ y ≤ 100

def IsOriginOrFirstPoint (x y : Int) : Bool :=
  (x == 0 && y == 0) || (x == 1 && y == 0)

def IsRightEdge (x y : Int) : Bool :=
  x >= 1 && -x + 1 < y && y <= x

def IsLeftEdge (x y : Int) : Bool :=
  x < 0 && x <= y && y < -x

def IsTopEdge (x y : Int) : Bool :=
  y > 0 && -y <= x && x < y

def ComputeTurns (x y : Int) : Int :=
  if IsOriginOrFirstPoint x y then 0
  else if IsRightEdge x y then 1 + 4 * (x - 1)
  else if IsLeftEdge x y then 3 + 4 * (-x - 1)
  else if IsTopEdge x y then 2 + 4 * (y - 1)
  else -4 * y

@[reducible, simp]
def solve_precond (x y : Int) : Prop :=
  ValidInput x y
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (x y : Int) (h_precond : solve_precond x y) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x y : Int) (result : Int) (h_precond : solve_precond x y) : Prop :=
  result ≥ 0 ∧
  result = ComputeTurns x y ∧
  (IsOriginOrFirstPoint x y = true → result = 0) ∧
  (IsRightEdge x y = true → result = 1 + 4 * (x - 1)) ∧
  (IsLeftEdge x y = true → result = 3 + 4 * (-x - 1)) ∧
  (IsTopEdge x y = true → result = 2 + 4 * (y - 1)) ∧
  (¬(IsOriginOrFirstPoint x y = true ∨ IsRightEdge x y = true ∨ IsLeftEdge x y = true ∨ IsTopEdge x y = true) → result = -4 * y)

theorem solve_spec_satisfied (x y : Int) (h_precond : solve_precond x y) :
    solve_postcond x y (solve x y h_precond) h_precond := by
  sorry
-- </vc-theorems>