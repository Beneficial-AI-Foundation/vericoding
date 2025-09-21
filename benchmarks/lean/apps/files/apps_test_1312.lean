-- <vc-preamble>
def ValidInput (n m : Int) : Prop :=
  n ≥ m ∧ m > 0

def sum (s : List Int) : Int :=
  match s with
  | [] => 0
  | h :: t => h + sum t

def count (s : List Int) (val : Int) : Int :=
  match s with
  | [] => 0
  | h :: t => (if h = val then 1 else 0) + count t val

def OptimalDistribution (result : List Int) (n m : Int) : Prop :=
  m > 0 →
  result.length = m ∧
  (∀ i, 0 ≤ i ∧ i < result.length → result[i]! > 0) ∧
  sum result = n ∧
  (∀ i, 0 ≤ i ∧ i < result.length → result[i]! = n / m ∨ result[i]! = n / m + 1) ∧
  count result (n / m) = m - (n % m) ∧
  count result (n / m + 1) = n % m

@[reducible, simp]
def solve_precond (n m : Int) : Prop :=
  ValidInput n m
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (h_precond : solve_precond n m) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (result : List Int) (h_precond : solve_precond n m) : Prop :=
  OptimalDistribution result n m

theorem solve_spec_satisfied (n m : Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  sorry
-- </vc-theorems>