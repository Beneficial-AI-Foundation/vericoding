-- <vc-preamble>
partial def AlternatingSum (n: Int) : Int :=
  if n = 1 then -1
  else if n > 1 then
    AlternatingSum (n-1) + (if n % 2 = 0 then n else -n)
  else 0

def ValidInput (n: Int) : Prop :=
  n > 0

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (_ : solve_precond n) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result: Int) (h_precond : solve_precond n) : Prop :=
  result = AlternatingSum n ∧ 
  (n % 2 = 0 → result = n / 2) ∧ 
  (n % 2 ≠ 0 → result = n / 2 - n)

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>