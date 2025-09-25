-- <vc-preamble>
def NormalizeAngle (angle : Int) : Int :=
  let n := angle % 360
  if n < 0 then n + 360 else n

def DeviationFromVertical (angle : Int) : Int :=
  if angle ≤ 180 then angle else 360 - angle

def ImageAngleAfterRotations (cameraAngle : Int) (rotations : Int) : Int :=
  NormalizeAngle (-cameraAngle + 90 * rotations)

def ImageDeviationAfterRotations (cameraAngle : Int) (rotations : Int) : Int :=
  DeviationFromVertical (ImageAngleAfterRotations cameraAngle rotations)

def IsOptimalRotations (cameraAngle : Int) (result : Int) : Prop :=
  0 ≤ result ∧ result ≤ 3 ∧
  ∀ k, 0 ≤ k ∧ k ≤ 3 → 
    let result_deviation := ImageDeviationAfterRotations cameraAngle result
    let k_deviation := ImageDeviationAfterRotations cameraAngle k
    result_deviation < k_deviation ∨ (result_deviation = k_deviation ∧ result ≤ k)

@[reducible, simp]
def solve_precond (x : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (x : Int) (h_precond : solve_precond x) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x : Int) (result: Int) (h_precond : solve_precond x) : Prop :=
  0 ≤ result ∧ result ≤ 3 ∧ IsOptimalRotations x result

theorem solve_spec_satisfied (x : Int) (h_precond : solve_precond x) :
    solve_postcond x (solve x h_precond) h_precond := by
  sorry
-- </vc-theorems>