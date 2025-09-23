-- <vc-preamble>
def ValidInput (n k : Int) (powers : List Int) : Prop :=
  n > 0 ∧ k > 0 ∧ k ≤ n ∧ n % k = 0 ∧ powers.length = n.natAbs

def IsOptimalStartingTask (result n k : Int) (powers : List Int) : Prop :=
  ValidInput n k powers → (1 ≤ result ∧ result ≤ k)

@[reducible, simp]
def solve_precond (n k : Int) (powers : List Int) : Prop :=
  ValidInput n k powers
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (powers : List Int) (h_precond : solve_precond n k powers) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (powers : List Int) (result : Int) (h_precond : solve_precond n k powers) : Prop :=
  IsOptimalStartingTask result n k powers

theorem solve_spec_satisfied (n k : Int) (powers : List Int) (h_precond : solve_precond n k powers) :
    solve_postcond n k powers (solve n k powers h_precond) h_precond := by
  sorry
-- </vc-theorems>