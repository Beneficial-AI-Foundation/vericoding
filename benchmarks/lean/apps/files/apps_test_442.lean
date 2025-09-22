-- <vc-preamble>
def H (x y : Int) : Int :=
  x * x + 2 * x * y + x + 1

def ValidInput (r : Int) : Prop :=
  r > 0

def ValidSolution (result : List Int) (r : Int) : Prop :=
  if result.length = 0 then
    True
  else
    result.length = 2 ∧ result[0]! > 0 ∧ result[1]! > 0 ∧ H result[0]! result[1]! = r

def HasSolution (r : Int) : Prop :=
  r > 4 ∧ r % 2 = 1

@[reducible, simp]
def solve_precond (r : Int) : Prop :=
  ValidInput r
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (r : Int) (h_precond : solve_precond r) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (r : Int) (result : List Int) (h_precond : solve_precond r) : Prop :=
  ValidSolution result r ∧
  (result.length = 0 ∨ result.length = 2) ∧
  (result.length = 2 → result[0]! > 0 ∧ result[1]! > 0) ∧
  (result.length = 2 → H result[0]! result[1]! = r) ∧
  (r ≤ 4 → result.length = 0) ∧
  (r > 4 ∧ r % 2 = 0 → result.length = 0) ∧
  (r > 4 ∧ r % 2 = 1 → result.length = 2 ∧ result[0]! = 1 ∧ result[1]! = (r - 3) / 2)

theorem solve_spec_satisfied (r : Int) (h_precond : solve_precond r) :
    solve_postcond r (solve r h_precond) h_precond := by
  sorry
-- </vc-theorems>