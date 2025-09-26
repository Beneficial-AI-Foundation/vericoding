-- <vc-preamble>
def mymax (a b : Int) : Int :=
  if a ≥ b then a else b

def ValidInput (a b x y z : Int) : Prop :=
  a ≥ 0 ∧ b ≥ 0 ∧ x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0

def YellowCrystalsNeeded (x y : Int) : Int :=
  x * 2 + y

def BlueCrystalsNeeded (y z : Int) : Int :=
  y + z * 3

def MinAdditionalCrystals (a b x y z : Int) : Int :=
  mymax 0 (YellowCrystalsNeeded x y - a) + mymax 0 (BlueCrystalsNeeded y z - b)

@[reducible, simp]
def solve_precond (a b x y z : Int) : Prop :=
  ValidInput a b x y z
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b x y z : Int) (h_precond : solve_precond a b x y z) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b x y z : Int) (result: Int) (h_precond : solve_precond a b x y z) : Prop :=
  result ≥ 0 ∧ result = MinAdditionalCrystals a b x y z

theorem solve_spec_satisfied (a b x y z : Int) (h_precond : solve_precond a b x y z) :
    solve_postcond a b x y z (solve a b x y z h_precond) h_precond := by
  sorry
-- </vc-theorems>