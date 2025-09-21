-- <vc-preamble>
def ValidInput (n : Int) (heights : List Int) : Prop :=
  n > 0 ∧ heights.length = n.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < n → heights.get! i.natAbs ≥ 0) ∧
  (∀ i, 0 ≤ i ∧ i < n - 1 → heights.get! i.natAbs < heights.get! (i + 1).natAbs)

def ValidOutput (n : Int) (result : List Int) : Prop :=
  result.length = n.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < n → result.get! i.natAbs ≥ 0) ∧
  (∀ i, 0 ≤ i ∧ i < n - 1 → result.get! i.natAbs ≤ result.get! (i + 1).natAbs) ∧
  (∀ i, 0 ≤ i ∧ i < n - 1 → result.get! (i + 1).natAbs - result.get! i.natAbs ≤ 1)

def IsStable (result : List Int) : Prop :=
  ∀ i, 0 ≤ i ∧ i < (result.length : Int) - 1 → ¬(result.get! i.natAbs + 2 ≤ result.get! (i + 1).natAbs)

def sum_seq (s : List Int) : Int :=
  s.sum

@[reducible, simp]
def solve_precond (n : Int) (heights : List Int) : Prop :=
  ValidInput n heights
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (heights : List Int) (h_precond : solve_precond n heights) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (heights : List Int) (result : List Int) (h_precond : solve_precond n heights) : Prop :=
  ValidOutput n result ∧
  sum_seq result = sum_seq heights ∧
  IsStable result

theorem solve_spec_satisfied (n : Int) (heights : List Int) (h_precond : solve_precond n heights) :
    solve_postcond n heights (solve n heights h_precond) h_precond := by
  sorry
-- </vc-theorems>