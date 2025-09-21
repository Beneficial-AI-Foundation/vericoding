-- <vc-preamble>
def ValidInput (n k : Int) (heights : List Int) : Prop :=
  n ≥ 1 ∧ k ≥ 1 ∧ heights.length = n ∧ 
  ∀ i, 0 ≤ i ∧ i < heights.length → heights[i]! ≥ 1

def CountEligible (heights : List Int) (k : Int) : Int :=
  (heights.filter (fun h => h ≥ k)).length

@[reducible, simp]
def solve_precond (n k : Int) (heights : List Int) : Prop :=
  ValidInput n k heights
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (heights : List Int) (h_precond : solve_precond n k heights) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (heights : List Int) (count : Int) (h_precond : solve_precond n k heights) : Prop :=
  0 ≤ count ∧ count ≤ heights.length ∧ count = CountEligible heights k

theorem solve_spec_satisfied (n k : Int) (heights : List Int) (h_precond : solve_precond n k heights) :
    solve_postcond n k heights (solve n k heights h_precond) h_precond := by
  sorry
-- </vc-theorems>