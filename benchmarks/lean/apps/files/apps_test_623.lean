-- <vc-preamble>
partial def CountValidMinutes (a b : Int) : Int :=
  if a ≤ 0 ∨ b ≤ 0 then 0
  else if a = 1 ∧ b = 1 then 0
  else (if a > 1 ∨ b > 1 then 1 else 0) + 
       CountValidMinutes (if a < b then a + 1 else a - 2) (if a < b then b - 2 else b + 1)

@[reducible, simp]
def solve_precond (a1 a2 : Int) : Prop :=
  a1 ≥ 1 ∧ a2 ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a1 a2 : Int) (_ : solve_precond a1 a2) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a1 a2 : Int) (result: Int) (h_precond : solve_precond a1 a2) : Prop :=
  result ≥ 0 ∧ result = CountValidMinutes a1 a2 ∧ (a1 = 1 ∧ a2 = 1 → result = 0)

theorem solve_spec_satisfied (a1 a2 : Int) (h_precond : solve_precond a1 a2) :
    solve_postcond a1 a2 (solve a1 a2 h_precond) h_precond := by
  sorry
-- </vc-theorems>