-- <vc-preamble>
def ValidInput (n : Int) (s : String) : Prop :=
  n ≥ 1 ∧ n ≤ 2000 ∧ s.length = n.natAbs ∧ 
  ∀ i, 0 ≤ i ∧ i < s.length → 'a' ≤ s.data.get! i ∧ s.data.get! i ≤ 'z'

def ValidOutput (result : String) (n : Int) : Prop :=
  result.length = n.natAbs ∧ 
  ∀ i, 0 ≤ i ∧ i < result.length → 'a' ≤ result.data.get! i ∧ result.data.get! i ≤ 'z'

def PreservesCharacters (s : String) (result : String) : Prop :=
  s.data.length = result.data.length ∧ 
  ∀ c, s.data.count c = result.data.count c

@[reducible, simp]
def solve_precond (n : Int) (s : String) : Prop :=
  ValidInput n s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (s : String) (h_precond : solve_precond n s) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (s : String) (result : String) (h_precond : solve_precond n s) : Prop :=
  ValidOutput result n ∧ PreservesCharacters s result

theorem solve_spec_satisfied (n : Int) (s : String) (h_precond : solve_precond n s) :
    solve_postcond n s (solve n s h_precond) h_precond := by
  sorry
-- </vc-theorems>