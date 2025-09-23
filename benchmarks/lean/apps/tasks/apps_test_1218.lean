-- <vc-preamble>
def ValidInput (n k : Int) : Prop :=
  n ≥ 1 ∧ k ≥ 2

def ImpossibilityCondition (n k : Int) (h : ValidInput n k) : Bool :=
  2 * (n - 1) - k * (k - 1) > 0

def ValidSolution (n k result : Int) (h : ValidInput n k) : Prop :=
  if ImpossibilityCondition n k h then
    result = -1
  else
    result ≥ 0 ∧ result ≤ k ∧
    ∃ x, x ≥ 0 ∧ 
         x * x - x + (2 * (n - 1) - k * (k - 1)) ≤ 0 ∧ 
         (x = 0 ∨ (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) > 0) ∧
         result = k - x

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  ValidInput n k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (h_precond : solve_precond n k) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (result : Int) (h_precond : solve_precond n k) : Prop :=
  result ≥ -1 ∧ 
  ((result = -1) ↔ ImpossibilityCondition n k h_precond) ∧
  ValidSolution n k result h_precond

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  sorry
-- </vc-theorems>