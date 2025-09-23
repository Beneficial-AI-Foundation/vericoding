-- <vc-preamble>
def validInput (a b c d : Int) : Prop :=
  0 ≤ a ∧ a < b ∧ b ≤ 100 ∧ 0 ≤ c ∧ c < d ∧ d ≤ 100

def myMin (x y : Int) : Int :=
  if x < y then x else y

def myMax (x y : Int) : Int :=
  if x > y then x else y

def intervalOverlapLength (a b c d : Int) : Int :=
  if myMin b d - myMax a c > 0 then myMin b d - myMax a c else 0

@[reducible, simp]
def solve_precond (a b c d : Int) : Prop :=
  validInput a b c d
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b c d : Int) (h_precond : solve_precond a b c d) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b c d : Int) (result: Int) (h_precond : solve_precond a b c d) : Prop :=
  result ≥ 0 ∧ result = intervalOverlapLength a b c d ∧ result ≤ 100

theorem solve_spec_satisfied (a b c d : Int) (h_precond : solve_precond a b c d) :
    solve_postcond a b c d (solve a b c d h_precond) h_precond := by
  sorry
-- </vc-theorems>