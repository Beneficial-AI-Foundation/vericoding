-- <vc-preamble>
def ValidRectangleParts (a b n : Int) : Prop :=
  a > 0 ∧ b > 0 ∧ a ≠ b ∧ 2 * a + 2 * b = n

def CountValidRectangles (n : Int) : Int :=
  if n % 2 = 1 then 0
  else if n % 4 = 2 then n / 4
  else n / 4 - 1

def ValidInput (n : Int) : Prop :=
  n > 0

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : Int) (h_precond : solve_precond n) : Prop :=
  result = CountValidRectangles n ∧
  (n % 2 = 1 → result = 0) ∧
  (n % 2 = 0 ∧ n % 4 = 2 → result = n / 4) ∧
  (n % 2 = 0 ∧ n % 4 = 0 → result = n / 4 - 1)

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>