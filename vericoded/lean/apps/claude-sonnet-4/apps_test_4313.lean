import Mathlib
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
-- LLM HELPER: Lemma to show SumOfPositiveProfits is always non-negative
lemma SumOfPositiveProfits_nonneg (values : List Int) (costs : List Int) (n : Nat) : 
  SumOfPositiveProfits values costs n ≥ 0 := by
  induction n with
  | zero => 
    unfold SumOfPositiveProfits
    simp
  | succ k ih => 
    unfold SumOfPositiveProfits
    simp only [Nat.succ_ne_zero, ite_false]
    -- We're in the else branch since k + 1 ≠ 0
    let profit := values[k]! - costs[k]!
    have h_sub : k + 1 - 1 = k := Nat.add_sub_cancel k 1
    simp only [h_sub]
    split_ifs with h_profit
    · -- profit > 0 case
      linarith [ih]
    · -- profit ≤ 0 case: we add 0
      simp
      exact ih
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (values : List Int) (costs : List Int) (h_precond : solve_precond n values costs) : Int :=
  SumOfPositiveProfits values costs n.toNat
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (values : List Int) (costs : List Int) (result : Int) (h_precond : solve_precond n values costs) : Prop :=
  result ≥ 0 ∧ result = SumOfPositiveProfits values costs n.toNat

theorem solve_spec_satisfied (n : Int) (values : List Int) (costs : List Int) (h_precond : solve_precond n values costs) :
    solve_postcond n values costs (solve n values costs h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · exact SumOfPositiveProfits_nonneg values costs n.toNat
  · rfl
-- </vc-theorems>
