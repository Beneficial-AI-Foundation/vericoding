-- <vc-preamble>
def ValidInput (r g b : Int) : Prop :=
  r ≥ 1 ∧ g ≥ 1 ∧ b ≥ 1

def MaxOf3 (r g b : Int) : Int :=
  if r ≥ g ∧ r ≥ b then r
  else if g ≥ r ∧ g ≥ b then g
  else b

def CanArrange (r g b : Int) (h : ValidInput r g b) : Bool :=
  let maxCount := MaxOf3 r g b
  let total := r + g + b
  2 * maxCount ≤ total + 1

@[reducible, simp]
def solve_precond (r g b : Int) : Prop :=
  ValidInput r g b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (r g b : Int) (h_precond : solve_precond r g b) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (r g b : Int) (result : Bool) (h_precond : solve_precond r g b) : Prop :=
  result = CanArrange r g b h_precond

theorem solve_spec_satisfied (r g b : Int) (h_precond : solve_precond r g b) :
    solve_postcond r g b (solve r g b h_precond) h_precond := by
  sorry
-- </vc-theorems>