-- <vc-preamble>
def ValidInput (n : Int) (s : String) : Prop :=
  n = s.length ∧ n ≥ 0

def IsGoodString (s : String) : Prop :=
  s.length % 2 = 0 ∧ ∀ i, 0 ≤ i ∧ i < s.length / 2 → s.get ⟨2*i⟩ ≠ s.get ⟨2*i+1⟩

@[reducible, simp]
def solve_precond (n : Int) (s : String) : Prop :=
  ValidInput n s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (s : String) (h_precond : solve_precond n s) : Int × String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (s : String) (result : Int × String) (h_precond : solve_precond n s) : Prop :=
  result.1 ≥ 0 ∧ 
  result.1 = s.length - result.2.length ∧ 
  IsGoodString result.2 ∧ 
  result.1 + result.2.length = s.length

theorem solve_spec_satisfied (n : Int) (s : String) (h_precond : solve_precond n s) :
    solve_postcond n s (solve n s h_precond) h_precond := by
  sorry
-- </vc-theorems>