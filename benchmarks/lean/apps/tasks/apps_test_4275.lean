-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length = 6 ∧ ∀ i, 0 ≤ i ∧ i < 6 → 'a' ≤ s.data[i]! ∧ s.data[i]! ≤ 'z'

def IsCoffeeLike (s : String) (h : ValidInput s) : Prop :=
  s.data[2]! = s.data[3]! ∧ s.data[4]! = s.data[5]!

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
  (result = "Yes" ∨ result = "No") ∧ (IsCoffeeLike s h_precond ↔ result = "Yes")

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>