-- <vc-preamble>
def minInt (a b : Int) : Int :=
  if a ≤ b then a else b

def computeInversions (n k iterations : Int) : Int :=
  if iterations ≤ 0 then 0
  else computeInversions n k (iterations - 1) + (n - 2*(iterations-1) - 1) + (n - 2*(iterations-1) - 2)
termination_by iterations.natAbs

def sumInversionsFormula (n iterations : Int) : Int :=
  if iterations ≤ 0 then 0
  else sumInversionsFormula n (iterations - 1) + (n - 2*(iterations-1) - 1) + (n - 2*(iterations-1) - 2)
termination_by iterations.natAbs

def sumOfConsecutivePairs (n k : Int) : Int :=
  let iterations := k
  if iterations = 0 then 0
  else sumInversionsFormula n iterations

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  n ≥ 1 ∧ k ≥ 0
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
  result ≥ 0 ∧
  result = computeInversions n k (minInt k (n / 2)) ∧
  result = sumInversionsFormula n (minInt k (n / 2)) ∧
  (k ≥ n / 2 → result = n * (n - 1) / 2) ∧
  (k < n / 2 → result = sumOfConsecutivePairs n k)

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  sorry
-- </vc-theorems>