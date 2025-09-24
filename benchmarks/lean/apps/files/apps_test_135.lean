-- <vc-preamble>
def ValidInput (n k : Int) : Prop :=
  n ≥ 1 ∧ k ≥ 1

def AllRemaindersDistinct (n k : Int) (h_valid : ValidInput n k) : Prop :=
  ∀ i, 1 ≤ i ∧ i ≤ k → n % i = (i - 1)

def HasNonDistinctRemainder (n k : Int) (h_valid : ValidInput n k) : Prop :=
  ∃ i, 1 ≤ i ∧ i ≤ k ∧ n % i ≠ (i - 1)

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  ValidInput n k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (h_precond : solve_precond n k) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (result : String) (h_precond : solve_precond n k) : Prop :=
  (result = "Yes\n" ↔ AllRemaindersDistinct n k h_precond) ∧
  (result = "No\n" ↔ HasNonDistinctRemainder n k h_precond)

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  sorry
-- </vc-theorems>