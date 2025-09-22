-- <vc-preamble>
def ValidInput (n m : Int) (tasks : List Int) : Prop :=
  n ≥ 2 ∧ m ≥ 1 ∧ tasks.length = m.natAbs ∧ 
  ∀ i, 0 ≤ i ∧ i < tasks.length → 1 ≤ tasks[i]! ∧ tasks[i]! ≤ n

def MinTimeToComplete (n : Int) (tasks : List Int) (currentPos : Int) (taskIndex : Int) : Int :=
  if h : 0 ≤ taskIndex ∧ taskIndex < tasks.length then
    let target := tasks[taskIndex.natAbs]!
    if target ≥ currentPos then target - currentPos
    else (n - currentPos) + target
  else 0

@[reducible, simp]
def solve_precond (n m : Int) (tasks : List Int) : Prop :=
  ValidInput n m tasks
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (tasks : List Int) (h_precond : solve_precond n m tasks) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (tasks : List Int) (result : Int) (h_precond : solve_precond n m tasks) : Prop :=
  result ≥ 0 ∧ 
  (m > 0 → result ≥ tasks[(m-1).natAbs]! - 1) ∧
  result ≤ (m - 1) * n + tasks[(m-1).natAbs]! - 1

theorem solve_spec_satisfied (n m : Int) (tasks : List Int) (h_precond : solve_precond n m tasks) :
    solve_postcond n m tasks (solve n m tasks h_precond) h_precond := by
  sorry
-- </vc-theorems>