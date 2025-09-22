-- <vc-preamble>
def AllEven (a : List Int) : Prop :=
  ∀ i, 0 ≤ i ∧ i < a.length → a[i]! % 2 = 0

def HasOdd (a : List Int) : Prop :=
  ∃ i, 0 ≤ i ∧ i < a.length ∧ a[i]! % 2 = 1

@[reducible, simp]
def solve_precond (a : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a : List Int) (h_precond : solve_precond a) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a : List Int) (result: String) (h_precond : solve_precond a) : Prop :=
  (result = "Second" ↔ AllEven a) ∧ 
  (result = "First" ↔ HasOdd a) ∧ 
  (result = "First" ∨ result = "Second")

theorem solve_spec_satisfied (a : List Int) (h_precond : solve_precond a) :
    solve_postcond a (solve a h_precond) h_precond := by
  sorry
-- </vc-theorems>