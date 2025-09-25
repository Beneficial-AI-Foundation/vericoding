-- <vc-preamble>
def ValidInput (x y z : Int) : Prop :=
  x ≥ 1 ∧ y ≥ 1 ∧ z ≥ 1 ∧ y + 2 * z ≤ x

def MaxPeople (x y z : Int) (h : ValidInput x y z) : Int :=
  (x - z) / (y + z)

def ValidSolution (x y z : Int) (result : Int) (h : ValidInput x y z) : Prop :=
  result = MaxPeople x y z h ∧
  result ≥ 0 ∧
  result * (y + z) ≤ x - z ∧ x - z < (result + 1) * (y + z)

@[reducible, simp]
def solve_precond (x y z : Int) : Prop :=
  ValidInput x y z
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (x y z : Int) (h_precond : solve_precond x y z) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x y z : Int) (result : Int) (h_precond : solve_precond x y z) : Prop :=
  ValidSolution x y z result h_precond

theorem solve_spec_satisfied (x y z : Int) (h_precond : solve_precond x y z) :
    solve_postcond x y z (solve x y z h_precond) h_precond := by
  sorry
-- </vc-theorems>