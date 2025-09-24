-- <vc-preamble>
axiom binomial : Int → Int → Int

@[reducible, simp]
def solve_precond (k : Int) : Prop :=
  0 ≤ k ∧ k ≤ 33
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (k : Int) (h_precond : solve_precond k) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (k : Int) (result : List Int) (h_precond : solve_precond k) : Prop :=
  result.length = k + 1 ∧
  (∀ i, 0 ≤ i ∧ i < result.length → result[i]! = binomial k i) ∧
  (∀ i, 0 ≤ i ∧ i < result.length → result[i]! > 0)

theorem solve_spec_satisfied (k : Int) (h_precond : solve_precond k) :
    solve_postcond k (solve k h_precond) h_precond := by
  sorry
-- </vc-theorems>