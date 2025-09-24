-- <vc-preamble>
def ValidInput (A B K : Int) : Prop :=
  A ≥ 0 ∧ B ≥ 0 ∧ K ≥ 0

def ExpectedTakahashiCookies (A B K : Int) (h : ValidInput A B K) : Int :=
  if A ≥ K then A - K else 0

def ExpectedAokiCookies (A B K : Int) (h : ValidInput A B K) : Int :=
  if A ≥ K then B
  else if K - A < B then B - (K - A)
  else 0

def CorrectResult (A B K takahashi aoki : Int) (h : ValidInput A B K) : Prop :=
  takahashi = ExpectedTakahashiCookies A B K h ∧
  aoki = ExpectedAokiCookies A B K h ∧
  takahashi ≥ 0 ∧ aoki ≥ 0

@[reducible, simp]
def solve_precond (A B K : Int) : Prop :=
  ValidInput A B K
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (A B K : Int) (h_precond : solve_precond A B K) : Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B K : Int) (result : Int × Int) (h_precond : solve_precond A B K) : Prop :=
  CorrectResult A B K result.1 result.2 h_precond

theorem solve_spec_satisfied (A B K : Int) (h_precond : solve_precond A B K) :
    solve_postcond A B K (solve A B K h_precond) h_precond := by
  sorry
-- </vc-theorems>