-- <vc-preamble>
def ValidInput (n m : Int) : Prop :=
  n ≥ 2 ∧ m ≥ 1 ∧ n ≤ m ∧ m ≤ 200000

def Combination (m n mod : Int) : Int := 0

def Power (base exp mod : Int) : Int := 0

def ExpectedResult (n m : Int) (h : ValidInput n m) : Int :=
  if n = 2 then 0
  else (((Combination m (n - 1) 998244353) * (n - 2)) % 998244353 * Power 2 (n - 3) 998244353) % 998244353

def ValidOutput (result : Int) : Prop :=
  0 ≤ result ∧ result < 998244353

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
  ValidOutput result ∧ result = ExpectedResult n m h_precond

theorem solve_spec_satisfied (n m : Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  sorry
-- </vc-theorems>