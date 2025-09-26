import Mathlib
-- <vc-preamble>
def CountOnesInBinary (n : Int) : Int :=
  if n ≤ 0 then 0
  else if n = 1 then 1
  else if n % 2 = 1 then 1 + CountOnesInBinary (n / 2)
  else CountOnesInBinary (n / 2)
termination_by n.natAbs

def ValidInput (x : Int) : Prop :=
  x ≥ 1

def ValidOutput (x : Int) (result : Int) : Prop :=
  ValidInput x ∧ result = CountOnesInBinary x

@[reducible, simp]
def solve_precond (x : Int) : Prop :=
  ValidInput x
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this problem
-- </vc-helpers>

-- <vc-definitions>
def solve (x : Int) (h_precond : solve_precond x) : Int :=
  CountOnesInBinary x
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x : Int) (result : Int) (h_precond : solve_precond x) : Prop :=
  ValidOutput x result

theorem solve_spec_satisfied (x : Int) (h_precond : solve_precond x) :
    solve_postcond x (solve x h_precond) h_precond := by
  unfold solve_postcond ValidOutput solve
  constructor
  · exact h_precond
  · rfl
-- </vc-theorems>
