-- <vc-preamble>
def Power (base : Int) (exp : Nat) : Int :=
  if exp = 0 then 1
  else base * Power base (exp - 1)

def ValidInput (n k : Int) : Prop :=
  1 ≤ n ∧ n ≤ 1000 ∧ 2 ≤ k ∧ k ≤ 1000

def PaintingWays (n k : Int) : Int :=
  k * Power (k - 1) (Int.natAbs (n - 1))

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  ValidInput n k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (h_precond : solve_precond n k) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (result : Int) (h_precond : solve_precond n k) : Prop :=
  result = PaintingWays n k ∧ result > 0

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  sorry
-- </vc-theorems>