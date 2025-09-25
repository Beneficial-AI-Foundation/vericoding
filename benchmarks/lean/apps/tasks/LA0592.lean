-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length ≥ 1 ∧ ∀ i, 0 ≤ i ∧ i < s.length → 'a' ≤ s.data[i]! ∧ s.data[i]! ≤ 'z'

def ExpectedLength (s : String) : Nat :=
  (s.length + 1) / 2

def CorrectExtraction (s : String) (result : String) : Prop :=
  result.length = ExpectedLength s ∧
  (∀ i, 0 ≤ i ∧ i < result.length → 0 ≤ 2*i ∧ 2*i < s.length ∧ result.data[i]! = s.data[2*i]!) ∧
  (∀ i, 0 ≤ i ∧ i < s.length ∧ i % 2 = 0 → ∃ j, 0 ≤ j ∧ j < result.length ∧ result.data[j]! = s.data[i]! ∧ j = i / 2)

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : String) (h_precond : solve_precond s) : Prop :=
  CorrectExtraction s result

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>