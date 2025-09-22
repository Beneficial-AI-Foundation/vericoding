-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length ≥ 1 ∧ s.length ≤ 100 ∧ ∀ i, 0 ≤ i ∧ i < s.length → 'a' ≤ s.data[i]! ∧ s.data[i]! ≤ 'z'

def ValidOutput (s : String) (result : String) : Prop :=
  result.length = s.length ∧ ∀ i, 0 ≤ i ∧ i < result.length → result.data[i]! = 'x'

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : String) (h_precond : solve_precond s) : Prop :=
  ValidOutput s result

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>