-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length ≥ 3

def CountExcessivePositionsHelper (s : String) (pos : Nat) (consecutiveX : Nat) : Nat :=
  if pos ≥ s.length then 0
  else
    let newConsecutiveX := if s.data.get! pos = 'x' then consecutiveX + 1 else 0
    let currentContribution := if newConsecutiveX > 2 then 1 else 0
    currentContribution + CountExcessivePositionsHelper s (pos + 1) newConsecutiveX

def CountExcessivePositions (s : String) : Nat :=
  CountExcessivePositionsHelper s 0 0

def ConsecutiveXCount (s : String) (pos : Nat) : Nat :=
  if pos = 0 then 0
  else if pos > 0 ∧ s.data.get! (pos - 1) = 'x' then 1 + ConsecutiveXCount s (pos - 1)
  else 0

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : Nat) (h_precond : solve_precond s) : Prop :=
  result ≤ s.length ∧ result = CountExcessivePositions s

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>