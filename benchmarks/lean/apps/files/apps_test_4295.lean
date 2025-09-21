-- <vc-preamble>
def ValidInput (n k : Int) : Prop :=
  n ≥ 0 ∧ k ≥ 1

def MinValue (n k : Int) (h : ValidInput n k) : Int :=
  let remainder := n % k
  let complement := k - remainder
  if remainder ≤ complement then remainder else complement

def IsCorrectResult (n k result : Int) (h : ValidInput n k) : Prop :=
  result = MinValue n k h ∧
  result ≥ 0 ∧
  result < k

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
  IsCorrectResult n k result h_precond

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  sorry
-- </vc-theorems>