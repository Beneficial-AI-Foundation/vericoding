-- <vc-preamble>
def ValidInput (n k : Int) : Prop :=
  n ≥ 1 ∧ k ≥ 1

def SheetsNeeded (n : Int) : (Int × Int × Int) :=
  (2 * n, 5 * n, 8 * n)

def TotalSheetsNeeded (n : Int) : Int :=
  2 * n + 5 * n + 8 * n

def CeilDiv (a b : Int) : Int :=
  (a + b - 1) / b

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
def solve_postcond (n k : Int) (result: Int) (h_precond : solve_precond n k) : Prop :=
  result = CeilDiv (2 * n) k + CeilDiv (5 * n) k + CeilDiv (8 * n) k ∧
  result ≥ 0 ∧
  result ≥ (TotalSheetsNeeded n + k - 1) / k

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  sorry
-- </vc-theorems>