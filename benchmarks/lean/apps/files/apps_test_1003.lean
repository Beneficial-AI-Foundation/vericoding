-- <vc-preamble>
def ValidInput (n m : Int) : Prop :=
  n ≥ 1 ∧ m ≥ 2

def SocksAfterDay (n m day : Int) : Int :=
  n + day / m - day

def CanWearSocksOnDay (n m day : Int) : Prop :=
  day ≥ 1 → SocksAfterDay n m (day - 1) > 0

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
  result ≥ n ∧ 
  result > 0 ∧ 
  SocksAfterDay n m result ≤ 0 ∧ 
  ∀ k, 1 ≤ k ∧ k < result → SocksAfterDay n m k > 0

theorem solve_spec_satisfied (n m : Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  sorry
-- </vc-theorems>