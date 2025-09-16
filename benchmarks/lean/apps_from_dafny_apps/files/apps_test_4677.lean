-- <vc-preamble>
-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length ≥ 1 ∧ s.length ≤ 10 ∧ ∀ i, i < s.length → s.data.get! i ∈ ['0', '1', 'B']

def SimulateKeystrokes (keystrokes : String) : String :=
  if keystrokes.length = 0 then ""
  else 
    let prev := SimulateKeystrokes (keystrokes.take (keystrokes.length - 1))
    let lastKey := keystrokes.data.get! (keystrokes.length - 1)
    if lastKey = 'B' then
      if prev.length > 0 then prev.take (prev.length - 1) else prev
    else
      prev ++ String.mk [lastKey]
termination_by keystrokes.length
decreasing_by simp_wf; sorry

def ValidOutput (result : String) : Prop :=
  ∀ i, i < result.length → result.data.get! i ∈ ['0', '1']

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : String) (h_precond : solve_precond s) : Prop :=
  ValidOutput result ∧ result = SimulateKeystrokes s

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>
