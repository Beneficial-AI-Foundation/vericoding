-- <vc-preamble>
-- Helper function definitions for power and sum calculations
def Power (base : Int) (exp : Int) : Int :=
  if exp ≤ 0 then 1 else base ^ exp.natAbs

def SumWithDecreasingPowers (n : Int) (start_power : Int) : Int :=
  if n ≤ 0 ∨ start_power ≤ 0 then 0 else n * start_power

def SumWithIncreasingPowers (n : Int) (max_power : Int) : Int :=
  if n ≤ 0 ∨ max_power ≤ 0 then 0 else n * max_power

def ValidInput (n l r : Int) : Prop :=
  n ≥ 1 ∧ l ≥ 1 ∧ r ≥ l ∧ r ≤ n ∧ r ≤ 20

def MinSumCalculation (n l : Int) : Int :=
  let start_power := Power 2 (l - 1)
  SumWithDecreasingPowers n start_power

def MaxSumCalculation (n r : Int) : Int :=
  let max_power := Power 2 (r - 1)
  SumWithIncreasingPowers n max_power

@[reducible, simp]
def solve_precond (n l r : Int) : Prop :=
  ValidInput n l r
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n l r : Int) (h_precond : solve_precond n l r) : Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n l r : Int) (result: Int × Int) (h_precond : solve_precond n l r) : Prop :=
  let min_sum := result.1
  let max_sum := result.2
  min_sum > 0 ∧ 
  max_sum > 0 ∧ 
  min_sum ≤ max_sum ∧ 
  min_sum = MinSumCalculation n l ∧ 
  max_sum = MaxSumCalculation n r

theorem solve_spec_satisfied (n l r : Int) (h_precond : solve_precond n l r) :
    solve_postcond n l r (solve n l r h_precond) h_precond := by
  sorry
-- </vc-theorems>