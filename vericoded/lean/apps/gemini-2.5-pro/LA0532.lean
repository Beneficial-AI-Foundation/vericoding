import Mathlib
-- <vc-preamble>
def ValidInput (n k : Int) : Prop :=
  n ≥ 1 ∧ k ≥ 1 ∧ n ≤ 100 ∧ k ≤ 100

def MinCrackerDifference (n k : Int) : Int :=
  if n % k = 0 then 0 else 1

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  ValidInput n k
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/--
`max_crackers n k` is the maximum number of crackers any person receives
when `n` crackers are distributed as evenly as possible among `k` people.
This is `n/k + 1` if there's a remainder, and `n/k` otherwise.
-/
def max_crackers (n k : Int) : Int :=
  if n % k = 0 then n / k else n / k + 1

-- LLM HELPER
/--
`min_crackers n k` is the minimum number of crackers any person receives
when `n` crackers are distributed as evenly as possible among `k` people.
This is always `n/k` (integer division).
-/
def min_crackers (n k : Int) : Int :=
  n / k

-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (h_precond : solve_precond n k) : Int :=
  if n % k = 0 then 0 else 1
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (result: Int) (h_precond : solve_precond n k) : Prop :=
  result = MinCrackerDifference n k ∧ 
  (result = 0 ↔ n % k = 0) ∧ 
  (result = 1 ↔ n % k ≠ 0)

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  unfold solve solve_postcond
  dsimp
  unfold MinCrackerDifference
  by_cases h_mod_eq_zero : n % k = 0
  · simp [h_mod_eq_zero]
  · simp [h_mod_eq_zero]
-- </vc-theorems>
