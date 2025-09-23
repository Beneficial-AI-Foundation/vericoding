-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  n ≥ 1

def CubesForLevel (level : Int) : Int :=
  level * (level + 1) / 2

def TotalCubesForHeight (h : Int) : Int :=
  h * (h + 1) * (h + 2) / 6

def ValidPyramidHeight (n h : Int) : Prop :=
  ValidInput n ∧ h ≥ 1 ∧ 
  TotalCubesForHeight h ≤ n ∧
  TotalCubesForHeight (h + 1) > n

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : Int) (h_precond : solve_precond n) : Prop :=
  result ≥ 1 ∧ ValidPyramidHeight n result

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>