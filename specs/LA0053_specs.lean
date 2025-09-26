-- <vc-preamble>

def ValidInput (a b x y : Int) : Prop :=
  a > 0 ∧ b > 0 ∧ x > 0 ∧ y > 0

def gcd (a b : Nat) : Nat :=
  if b = 0 then a else gcd b (a % b)
termination_by b
decreasing_by
  simp_wf
  exact Nat.mod_lt a (Nat.pos_of_ne_zero (fun h => by simp [h] at *))

def mymin (a b : Int) : Int :=
  if a ≤ b then a else b

def ExpectedResult (a b x y : Int) : Int :=
  let g := Int.natAbs (gcd (Int.natAbs x) (Int.natAbs y))
  let x_reduced := x / g
  let y_reduced := y / g
  mymin (a / x_reduced) (b / y_reduced)

@[reducible, simp]
def solve_precond (a b x y : Int) : Prop :=
  ValidInput a b x y
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b x y : Int) (h_precond : solve_precond a b x y) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b x y : Int) (result : Int) (h_precond : solve_precond a b x y) : Prop :=
  result ≥ 0 ∧ result = ExpectedResult a b x y

theorem solve_spec_satisfied (a b x y : Int) (h_precond : solve_precond a b x y) :
    solve_postcond a b x y (solve a b x y h_precond) h_precond := by
  sorry
-- </vc-theorems>