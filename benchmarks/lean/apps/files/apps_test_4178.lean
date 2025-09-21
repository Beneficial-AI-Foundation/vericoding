-- <vc-preamble>
def maxHeightUpTo (heights: List Int) (index: Nat) : Int :=
  if index = 0 then heights[0]!
  else if heights[index]! > maxHeightUpTo heights (index - 1) 
    then heights[index]!
    else maxHeightUpTo heights (index - 1)
termination_by index

def ValidInput (n: Int) (heights: List Int) : Prop :=
  n ≥ 1 ∧ heights.length = n.toNat ∧ (∀ i, i < heights.length → heights[i]! ≥ 1)

def CanMakeNonDecreasing (heights: List Int) : Prop :=
  heights.length > 0 ∧ (∀ i, i < heights.length → heights[i]! ≥ maxHeightUpTo heights i - 1)

@[reducible, simp]
def solve_precond (n: Int) (heights: List Int) : Prop :=
  ValidInput n heights
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n: Int) (heights: List Int) (h_precond : solve_precond n heights) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n: Int) (heights: List Int) (result: String) (h_precond : solve_precond n heights) : Prop :=
  (result = "Yes") ↔ CanMakeNonDecreasing heights

theorem solve_spec_satisfied (n: Int) (heights: List Int) (h_precond : solve_precond n heights) :
    solve_postcond n heights (solve n heights h_precond) h_precond := by
  sorry
-- </vc-theorems>