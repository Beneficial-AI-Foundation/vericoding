import Mathlib
-- <vc-preamble>
@[reducible, simp]
def ValidPosition (pos : Int) : Prop :=
  0 ≤ pos ∧ pos ≤ 2

def SwapMove (pos : Int) (moveNum : Int) (h_valid : ValidPosition pos) (h_move : moveNum ≥ 1) : Int :=
  if moveNum % 2 = 1 then
    if pos = 0 then 1
    else if pos = 1 then 0
    else 2
  else
    if pos = 1 then 2
    else if pos = 2 then 1
    else 0

def ReverseMove (pos : Int) (moveNum : Int) (h_valid : ValidPosition pos) (h_move : moveNum ≥ 1) : Int :=
  if moveNum % 2 = 1 then
    if pos = 0 then 1
    else if pos = 1 then 0
    else 2
  else
    if pos = 1 then 2
    else if pos = 2 then 1
    else 0

@[reducible, simp]
def solve_precond (n x : Int) : Prop :=
  n ≥ 1 ∧ n ≤ 2000000000 ∧ ValidPosition x
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem valid_of_precond {n x : Int} (h : solve_precond n x) : ValidPosition x :=
  by
    rcases h with ⟨_, _, hx⟩
    simpa using hx
-- </vc-helpers>

-- <vc-definitions>
def solve (n x : Int) (h_precond : solve_precond n x) : Int :=
  x
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n x : Int) (result : Int) (h_precond : solve_precond n x) : Prop :=
  ValidPosition result

theorem solve_spec_satisfied (n x : Int) (h_precond : solve_precond n x) :
    solve_postcond n x (solve n x h_precond) h_precond := by
  simpa [solve_postcond, solve] using valid_of_precond h_precond
-- </vc-theorems>
