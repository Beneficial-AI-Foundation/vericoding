-- <vc-preamble>
def ValidInput (n m : Int) (scores : List Int) : Prop :=
  n ≥ 1 ∧ m ≥ 1 ∧ scores.length = n.natAbs ∧
  ∀ i, 0 ≤ i ∧ i < scores.length → 0 ≤ scores[i]! ∧ scores[i]! ≤ m

def ListSum (nums : List Int) : Int :=
  nums.sum

def intMin (a b : Int) : Int :=
  if a ≤ b then a else b

def ValidRedistribution (original redistributed : List Int) (m : Int) : Prop :=
  redistributed.length = original.length ∧
  ListSum redistributed = ListSum original ∧
  ∀ i, 0 ≤ i ∧ i < redistributed.length → 0 ≤ redistributed[i]! ∧ redistributed[i]! ≤ m

def MaxPossibleFirstScore (n m : Int) (scores : List Int) : Int :=
  intMin (ListSum scores) m

@[reducible, simp]
def solve_precond (n m : Int) (scores : List Int) : Prop :=
  ValidInput n m scores
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (scores : List Int) (h_precond : solve_precond n m scores) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (scores : List Int) (result : Int) (h_precond : solve_precond n m scores) : Prop :=
  result = MaxPossibleFirstScore n m scores ∧
  result = intMin (ListSum scores) m ∧
  ∃ redistributed, ValidRedistribution scores redistributed m ∧ redistributed[0]! = result

theorem solve_spec_satisfied (n m : Int) (scores : List Int) (h_precond : solve_precond n m scores) :
    solve_postcond n m scores (solve n m scores h_precond) h_precond := by
  sorry
-- </vc-theorems>