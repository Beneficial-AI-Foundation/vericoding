-- <vc-preamble>

def ValidInput (k n s p : Int) : Prop :=
  k ≥ 1 ∧ n ≥ 1 ∧ s ≥ 1 ∧ p ≥ 1 ∧
  k ≤ 10000 ∧ n ≤ 10000 ∧ s ≤ 10000 ∧ p ≤ 10000

def SheetsPerPerson (n s : Int) : Int :=
  (n + s - 1) / s

def TotalSheetsNeeded (k n s : Int) : Int :=
  k * SheetsPerPerson n s

def MinPacksNeeded (k n s p : Int) : Int :=
  (TotalSheetsNeeded k n s + p - 1) / p

def CorrectResult (result k n s p : Int) : Prop :=
  result = MinPacksNeeded k n s p ∧
  result * p ≥ TotalSheetsNeeded k n s ∧
  (result - 1) * p < TotalSheetsNeeded k n s

@[reducible, simp]
def solve_precond (k n s p : Int) : Prop :=
  ValidInput k n s p
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (k n s p : Int) (h_precond : solve_precond k n s p) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (k n s p : Int) (result: Int) (h_precond : solve_precond k n s p) : Prop :=
  result ≥ 1 ∧ CorrectResult result k n s p

theorem solve_spec_satisfied (k n s p : Int) (h_precond : solve_precond k n s p) :
    solve_postcond k n s p (solve k n s p h_precond) h_precond := by
  sorry
-- </vc-theorems>