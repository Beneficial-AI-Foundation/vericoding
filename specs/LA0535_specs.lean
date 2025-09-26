-- <vc-preamble>
def SumOfPositiveProfits (values : List Int) (costs : List Int) (n : Nat) : Int :=
  if n = 0 then 0
  else 
    let profit := values[n-1]! - costs[n-1]!
    SumOfPositiveProfits values costs (n-1) + (if profit > 0 then profit else 0)

def ValidInput (n : Int) (values : List Int) (costs : List Int) : Prop :=
  values.length = n.toNat ∧ costs.length = n.toNat ∧ n ≥ 0

@[reducible, simp]
def solve_precond (n : Int) (values : List Int) (costs : List Int) : Prop :=
  ValidInput n values costs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (values : List Int) (costs : List Int) (h_precond : solve_precond n values costs) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (values : List Int) (costs : List Int) (result : Int) (h_precond : solve_precond n values costs) : Prop :=
  result ≥ 0 ∧ result = SumOfPositiveProfits values costs n.toNat

theorem solve_spec_satisfied (n : Int) (values : List Int) (costs : List Int) (h_precond : solve_precond n values costs) :
    solve_postcond n values costs (solve n values costs h_precond) h_precond := by
  sorry
-- </vc-theorems>