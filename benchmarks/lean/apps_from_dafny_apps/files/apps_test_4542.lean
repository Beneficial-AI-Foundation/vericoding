-- <vc-preamble>
-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < s.length → s.data[i]! = 'B' ∨ s.data[i]! = 'W'

def CountSegments (s : String) : Int := sorry

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
def solve (s : String) (h_precond : solve_precond s) : Int :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result: Int) (h_precond : solve_precond s) : Prop :=
  result ≥ 0 ∧ result = CountSegments s - 1 ∧ result ≤ s.length - 1

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>
