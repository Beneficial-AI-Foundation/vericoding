-- <vc-preamble>
def comb2 (n : Int) : Int :=
  n * (n - 1) / 2

def ValidInput (n m : Int) : Prop :=
  1 ≤ m ∧ m ≤ n

def MinFriendshipPairs (n m : Int) : Int :=
  let k := n / m
  let p := n % m
  p * comb2 (k + 1) + (m - p) * comb2 k

def MaxFriendshipPairs (n m : Int) : Int :=
  comb2 (n - m + 1)

@[reducible, simp]
def solve_precond (n m : Int) : Prop :=
  ValidInput n m
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (h_precond : solve_precond n m) : Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (result : Int × Int) (h_precond : solve_precond n m) : Prop :=
  let min_pairs := result.1
  let max_pairs := result.2
  min_pairs ≥ 0 ∧ 
  max_pairs ≥ 0 ∧ 
  min_pairs ≤ max_pairs ∧ 
  min_pairs = MinFriendshipPairs n m ∧ 
  max_pairs = MaxFriendshipPairs n m

theorem solve_spec_satisfied (n m : Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  sorry
-- </vc-theorems>