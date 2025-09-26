-- <vc-preamble>
def ValidInput (n m : Int) : Prop :=
  n > 0 ∧ n ≤ 10000 ∧ m > 1 ∧ m ≤ 10

def MinMoves (n : Int) : Int :=
  if n % 2 = 0 then n / 2 else n / 2 + 1

def ValidMoveCount (n k : Int) : Prop :=
  MinMoves n ≤ k ∧ k ≤ n

def IsValidSolution (n m result : Int) : Prop :=
  result = -1 ∨ (result > 0 ∧ result % m = 0 ∧ ValidMoveCount n result)

def NoSmallerSolution (n m result : Int) : Prop :=
  result = -1 → ∀ k, (MinMoves n ≤ k ∧ k ≤ n) → k % m ≠ 0

def IsMinimalSolution (n m result : Int) : Prop :=
  result ≠ -1 → ∀ k, (MinMoves n ≤ k ∧ k ≤ n ∧ k < result) → k % m ≠ 0

@[reducible, simp]
def solve_precond (n m : Int) : Prop :=
  ValidInput n m
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (h_precond : solve_precond n m) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (result : Int) (h_precond : solve_precond n m) : Prop :=
  IsValidSolution n m result ∧ NoSmallerSolution n m result ∧ IsMinimalSolution n m result

theorem solve_spec_satisfied (n m : Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  sorry
-- </vc-theorems>