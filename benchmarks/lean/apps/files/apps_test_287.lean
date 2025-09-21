-- <vc-preamble>

@[reducible, simp]
def ValidInput (n k : Int) : Prop :=
  n ≥ 1 ∧ k ≥ 0 ∧ k ≤ n

@[reducible, simp]
def ValidOutput (result : List Int) (n k : Int) : Prop :=
  result.length = 2 ∧ 
  result[0]! ≥ 0 ∧ 
  result[1]! ≥ 0 ∧ 
  result[0]! ≤ result[1]! ∧
  result[0]! ≤ n - k ∧
  result[1]! ≤ n - k

def MinGoodApartments (n k : Int) (h : ValidInput n k) : Int :=
  if k = 0 ∨ k = n then 0 else 1

def MaxGoodApartments (n k : Int) (h : ValidInput n k) : Int :=
  if k = 0 ∨ k = n then 0
  else if n - k < k * 2 then n - k
  else k * 2

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  ValidInput n k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (h_precond : solve_precond n k) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (result : List Int) (h_precond : solve_precond n k) : Prop :=
  ValidOutput result n k ∧
  result[0]! = MinGoodApartments n k h_precond ∧
  result[1]! = MaxGoodApartments n k h_precond

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  sorry
-- </vc-theorems>