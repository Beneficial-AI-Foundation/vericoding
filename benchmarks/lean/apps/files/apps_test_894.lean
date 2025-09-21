-- <vc-preamble>
def ValidInput (x y : Int) : Prop :=
  x ≠ 0 ∧ y ≠ 0

def ValidOutput (result : List Int) (x y : Int) : Prop :=
  result.length = 4 ∧
  result[0]! < result[2]! ∧
  (x * y > 0 ∧ x < 0 → result = [x + y, 0, 0, x + y]) ∧
  (x * y > 0 ∧ x ≥ 0 → result = [0, x + y, x + y, 0]) ∧
  (x * y ≤ 0 ∧ x < 0 → result = [x - y, 0, 0, y - x]) ∧
  (x * y ≤ 0 ∧ x ≥ 0 → result = [0, y - x, x - y, 0])

@[reducible, simp]
def solve_precond (x y : Int) : Prop :=
  ValidInput x y
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (x y : Int) (h_precond : solve_precond x y) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x y : Int) (result : List Int) (h_precond : solve_precond x y) : Prop :=
  ValidOutput result x y

theorem solve_spec_satisfied (x y : Int) (h_precond : solve_precond x y) :
    solve_postcond x y (solve x y h_precond) h_precond := by
  sorry
-- </vc-theorems>