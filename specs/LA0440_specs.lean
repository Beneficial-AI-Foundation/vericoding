-- <vc-preamble>
def ValidInput (angles : List Int) : Prop :=
  ∀ i, 0 ≤ i ∧ i < angles.length → 1 ≤ angles[i]! ∧ angles[i]! < 180

def ComputeAnswer (angle : Int) : Int :=
  let g := Int.gcd angle 180
  let de_over_g := angle / g
  let n180_over_g := 180 / g
  if de_over_g = n180_over_g - 1 then n180_over_g * 2 else n180_over_g

def CorrectOutput (angles : List Int) (result : List Int) : Prop :=
  ValidInput angles →
  result.length = angles.length ∧
  ∀ i, 0 ≤ i ∧ i < angles.length → result[i]! = ComputeAnswer angles[i]!

@[reducible, simp]
def solve_precond (angles : List Int) : Prop :=
  ValidInput angles
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (angles : List Int) (h_precond : solve_precond angles) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (angles : List Int) (result : List Int) (h_precond : solve_precond angles) : Prop :=
  CorrectOutput angles result

theorem solve_spec_satisfied (angles : List Int) (h_precond : solve_precond angles) :
    solve_postcond angles (solve angles h_precond) h_precond := by
  sorry
-- </vc-theorems>