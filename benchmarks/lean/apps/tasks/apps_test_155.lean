-- <vc-preamble>
@[reducible, simp]
def ValidInput (n m k : Int) : Prop :=
  n ≥ 2 ∧ m ≥ 2 ∧ n % 2 = 0 ∧ k ≥ 0 ∧ k < n * m

@[reducible, simp]
def ValidOutput (result : List Int) (n m : Int) : Prop :=
  result.length = 2 ∧ result[0]! ≥ 1 ∧ result[0]! ≤ n ∧ result[1]! ≥ 1 ∧ result[1]! ≤ m

@[reducible, simp]
def CorrectPosition (result : List Int) (n m k : Int) : Prop :=
  ValidInput n m k ∧ result.length = 2 ∧
  (if k < n then
    result[0]! = k + 1 ∧ result[1]! = 1
  else
    let k_remaining := k - n
    let r := n - k_remaining / (m - 1)
    result[0]! = r ∧
    (r % 2 = 1 → result[1]! = m - k_remaining % (m - 1)) ∧
    (r % 2 = 0 → result[1]! = 2 + k_remaining % (m - 1)))

@[reducible, simp]
def solve_precond (n m k : Int) : Prop :=
  ValidInput n m k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m k : Int) (h_precond : solve_precond n m k) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m k : Int) (result : List Int) (h_precond : solve_precond n m k) : Prop :=
  ValidOutput result n m ∧ CorrectPosition result n m k

theorem solve_spec_satisfied (n m k : Int) (h_precond : solve_precond n m k) :
    solve_postcond n m k (solve n m k h_precond) h_precond := by
  sorry
-- </vc-theorems>