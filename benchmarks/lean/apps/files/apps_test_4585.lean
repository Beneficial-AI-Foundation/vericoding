-- <vc-preamble>
def ValidInput (x : Int) : Prop :=
  x ≥ 1

def TriangularNumber (n : Int) : Int :=
  n * (n + 1) / 2

def IsMinimalTime (t : Int) (x : Int) : Prop :=
  t ≥ 1 ∧ 
  TriangularNumber t ≥ x ∧
  (t = 1 ∨ TriangularNumber (t - 1) < x)

@[reducible, simp]
def solve_precond (x : Int) : Prop :=
  ValidInput x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (x : Int) (h_precond : solve_precond x) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x : Int) (result : Int) (h_precond : solve_precond x) : Prop :=
  IsMinimalTime result x

theorem solve_spec_satisfied (x : Int) (h_precond : solve_precond x) :
    solve_postcond x (solve x h_precond) h_precond := by
  sorry
-- </vc-theorems>