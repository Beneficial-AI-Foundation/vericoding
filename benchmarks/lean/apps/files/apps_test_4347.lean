-- <vc-preamble>
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def ValidInput (n : Int) : Prop :=
  n ≥ 2 ∧ n % 2 = 0 ∧ n ≤ 20

def ExpectedResult (n : Int) : Int :=
  let half := n / 2
  let factN := factorial n.natAbs
  let factHalf := factorial half.natAbs
  let factHalfMinus1 := factorial (half - 1).natAbs
  let binomial := factN / (factHalf * factHalf)
  let arrangements := factHalfMinus1 * factHalfMinus1
  (binomial * arrangements) / 2

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
def solve_postcond (n : Int) (result: Int) (h_precond : solve_precond n) : Prop :=
  result = ExpectedResult n ∧ result > 0

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>