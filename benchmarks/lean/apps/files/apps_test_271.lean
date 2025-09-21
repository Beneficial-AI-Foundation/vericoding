-- <vc-preamble>
def ValidResult (n : Int) (result : Int) (h : n ≥ 0) : Prop :=
  let quotient := n / 10
  let remainder := n % 10
  result % 10 = 0 ∧ 
  result ≥ 0 ∧
  (remainder < 5 → result = quotient * 10) ∧
  (remainder > 5 → result = (quotient + 1) * 10) ∧
  (remainder = 5 → ((quotient % 2 = 0 → result = quotient * 10) ∧ 
                    (quotient % 2 = 1 → result = (quotient + 1) * 10)))

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  n ≥ 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : Int) (h_precond : solve_precond n) : Prop :=
  ValidResult n result h_precond

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>