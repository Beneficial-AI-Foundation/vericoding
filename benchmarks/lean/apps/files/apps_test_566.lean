-- <vc-preamble>
def ValidInput (r g b : Int) : Prop :=
  r ≥ 0 ∧ g ≥ 0 ∧ b ≥ 0

def mymin (a b : Int) : Int :=
  if a ≤ b then a else b

def MaxTables (r g b : Int) : Int :=
  mymin (mymin (mymin ((r + g + b) / 3) (r + g)) (r + b)) (g + b)

@[reducible, simp]
def solve_precond (r g b : Int) : Prop :=
  ValidInput r g b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (r g b : Int) (h_precond : solve_precond r g b) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (r g b : Int) (result : Int) (h_precond : solve_precond r g b) : Prop :=
  result = MaxTables r g b ∧ result ≥ 0

theorem solve_spec_satisfied (r g b : Int) (h_precond : solve_precond r g b) :
    solve_postcond r g b (solve r g b h_precond) h_precond := by
  sorry
-- </vc-theorems>