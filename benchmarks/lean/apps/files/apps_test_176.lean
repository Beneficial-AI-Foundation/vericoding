-- <vc-preamble>
def ValidInput (k a b : Int) : Prop :=
  k > 0 ∧ a ≤ b

def FloorDiv (a b : Int) : Int :=
  if a ≥ 0 then a / b
  else (a - b + 1) / b

def CountDivisiblesInRange (k a b : Int) : Int :=
  FloorDiv b k - FloorDiv (a - 1) k

@[reducible, simp]
def solve_precond (k a b : Int) : Prop :=
  ValidInput k a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (k a b : Int) (h_precond : solve_precond k a b) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (k a b : Int) (result : Int) (h_precond : solve_precond k a b) : Prop :=
  result ≥ 0 ∧ result = CountDivisiblesInRange k a b

theorem solve_spec_satisfied (k a b : Int) (h_precond : solve_precond k a b) :
    solve_postcond k a b (solve k a b h_precond) h_precond := by
  sorry
-- </vc-theorems>