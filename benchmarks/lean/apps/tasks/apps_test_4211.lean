-- <vc-preamble>
def ValidInput (n : Int) (b : List Int) : Prop :=
  n ≥ 2 ∧ b.length = n - 1 ∧ ∀ i, 0 ≤ i ∧ i < b.length → b[i]! ≥ 0

def sum_mins (b : List Int) (len : Int) : Int := 0

def CorrectResult (n : Int) (b : List Int) (result : Int) : Prop :=
  if n = 2 then
    result = 2 * b[0]!
  else
    result = b[0]! + b[Int.natAbs (n-2)]! + sum_mins b (n-2)

@[reducible, simp]
def solve_precond (n : Int) (b : List Int) : Prop :=
  ValidInput n b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (b : List Int) (_ : solve_precond n b) : Int :=
  0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (b : List Int) (result : Int) (_ : solve_precond n b) : Prop :=
  CorrectResult n b result

theorem solve_spec_satisfied (n : Int) (b : List Int) (h_precond : solve_precond n b) :
    solve_postcond n b (solve n b h_precond) h_precond := by
  sorry
-- </vc-theorems>