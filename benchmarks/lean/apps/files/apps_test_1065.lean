-- <vc-preamble>
def ValidInput (n k M D : Int) : Prop :=
  2 ≤ n ∧ 2 ≤ k ∧ k ≤ n ∧ 1 ≤ M ∧ M ≤ n ∧ 1 ≤ D ∧ D ≤ n ∧ M * D * k ≥ n

def CandiesUsed (x d k : Int) : Int :=
  x * ((d - 1) * k + 1)

def ValidDistribution (x d n k M D : Int) : Prop :=
  1 ≤ x ∧ x ≤ M ∧ 1 ≤ d ∧ d ≤ D ∧ CandiesUsed x d k ≤ n

def Person1Candies (x d : Int) : Int :=
  x * d

@[reducible, simp]
def solve_precond (n k M D : Int) : Prop :=
  ValidInput n k M D
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k M D : Int) (h_precond : solve_precond n k M D) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k M D : Int) (result : Int) (h_precond : solve_precond n k M D) : Prop :=
  result ≥ 0 ∧ 
  result ≤ M * D ∧
  (∀ x d, ValidDistribution x d n k M D → Person1Candies x d ≤ result) ∧
  (∃ x d, ValidDistribution x d n k M D ∧ Person1Candies x d = result)

theorem solve_spec_satisfied (n k M D : Int) (h_precond : solve_precond n k M D) :
    solve_postcond n k M D (solve n k M D h_precond) h_precond := by
  sorry
-- </vc-theorems>