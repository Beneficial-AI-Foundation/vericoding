-- <vc-preamble>
def ValidInput (n t : Int) : Prop :=
  1 ≤ n ∧ n ≤ 10 ∧ 0 ≤ t ∧ t ≤ 10000

def TotalGlasses (n : Int) : Int :=
  n * (n + 1) / 2

def ValidResult (result n t : Int) : Prop :=
  result ≥ 0 ∧ result ≤ TotalGlasses n

def CorrectForEdgeCases (result n t : Int) : Prop :=
  (t = 0 → result = 0) ∧
  (n = 1 ∧ t ≥ 1 → result = 1) ∧
  (n = 1 ∧ t = 0 → result = 0) ∧
  (t ≥ 1 ∧ n > 1 → result ≥ 1)

@[reducible, simp]
def solve_precond (n t : Int) : Prop :=
  ValidInput n t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n t : Int) (h_precond : solve_precond n t) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n t : Int) (result : Int) (h_precond : solve_precond n t) : Prop :=
  ValidResult result n t ∧ CorrectForEdgeCases result n t

theorem solve_spec_satisfied (n t : Int) (h_precond : solve_precond n t) :
    solve_postcond n t (solve n t h_precond) h_precond := by
  sorry
-- </vc-theorems>