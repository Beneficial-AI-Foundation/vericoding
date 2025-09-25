-- <vc-preamble>
def ValidInput (n : Int) (times : List Int) (T : Int) : Prop :=
  n ≥ 1 ∧ times.length = n ∧ T ≥ 1 ∧ 
  ∀ i, 0 ≤ i ∧ i < times.length → 1 ≤ times.get! i ∧ times.get! i ≤ 1000

def countStudentsInWindowHelper (times : List Int) (start : Int) (T : Int) (index : Nat) : Int :=
  if h : index < times.length then
    let countRest := countStudentsInWindowHelper times start T (index + 1)
    let timeAtIndex := times.get ⟨index, h⟩
    if start ≤ timeAtIndex ∧ timeAtIndex ≤ start + T - 1 then countRest + 1 else countRest
  else 0
termination_by times.length - index

def countStudentsInWindow (times : List Int) (start : Int) (T : Int) : Int :=
  countStudentsInWindowHelper times start T 0

def maxStudentsInWindowUpTo (times : List Int) (T : Int) (maxStart : Nat) : Int :=
  if maxStart = 0 then 0
  else
    let count := countStudentsInWindow times maxStart T
    let restMax := maxStudentsInWindowUpTo times T (maxStart - 1)
    if count > restMax then count else restMax
termination_by maxStart

def maxStudentsInWindow (times : List Int) (T : Int) : Int :=
  maxStudentsInWindowUpTo times T 1000

@[reducible, simp]
def solve_precond (n : Int) (times : List Int) (T : Int) : Prop :=
  ValidInput n times T
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (times : List Int) (T : Int) (h_precond : solve_precond n times T) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (times : List Int) (T : Int) (result : Int) (h_precond : solve_precond n times T) : Prop :=
  result ≥ 0 ∧ result ≤ n ∧ result = maxStudentsInWindow times T

theorem solve_spec_satisfied (n : Int) (times : List Int) (T : Int) (h_precond : solve_precond n times T) :
    solve_postcond n times T (solve n times T h_precond) h_precond := by
  sorry
-- </vc-theorems>