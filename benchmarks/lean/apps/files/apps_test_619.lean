-- <vc-preamble>
def ValidInput (x y z : Int) : Prop :=
  x ≥ 0 ∧ y ≥ 0 ∧ z > 0

def MaxCoconuts (x y z : Int) (h : ValidInput x y z) : Int :=
  (x + y) / z

def MinExchange (x y z : Int) (h : ValidInput x y z) : Int :=
  let rx := x % z
  let ry := y % z
  if rx + ry < z then 0
  else z - (if rx > ry then rx else ry)

@[reducible, simp]
def solve_precond (x y z : Int) : Prop :=
  ValidInput x y z
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (x y z : Int) (h_precond : solve_precond x y z) : Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x y z : Int) (result : Int × Int) (h_precond : solve_precond x y z) : Prop :=
  let coconuts := result.1
  let exchange := result.2
  coconuts = MaxCoconuts x y z h_precond ∧
  exchange = MinExchange x y z h_precond ∧
  coconuts ≥ x / z + y / z ∧
  coconuts ≤ x / z + y / z + 1 ∧
  exchange ≥ 0 ∧ exchange < z

theorem solve_spec_satisfied (x y z : Int) (h_precond : solve_precond x y z) :
    solve_postcond x y z (solve x y z h_precond) h_precond := by
  sorry
-- </vc-theorems>