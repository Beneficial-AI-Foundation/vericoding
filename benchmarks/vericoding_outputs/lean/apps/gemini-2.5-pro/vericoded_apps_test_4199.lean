import Mathlib
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
-- LLM HELPER
theorem CountEligible_nonneg (heights : List Int) (k : Int) : 0 ≤ CountEligible heights k := by
  unfold CountEligible
  exact Int.natCast_nonneg _

-- LLM HELPER
theorem CountEligible_le_length (heights : List Int) (k : Int) : CountEligible heights k ≤ heights.length := by
  unfold CountEligible
  rw [Nat.cast_le]
  apply List.length_filter_le
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (heights : List Int) (h_precond : solve_precond n k heights) : Int :=
  CountEligible heights k
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (heights : List Int) (count : Int) (h_precond : solve_precond n k heights) : Prop :=
  0 ≤ count ∧ count ≤ heights.length ∧ count = CountEligible heights k

theorem solve_spec_satisfied (n k : Int) (heights : List Int) (h_precond : solve_precond n k heights) :
    solve_postcond n k heights (solve n k heights h_precond) h_precond := by
   simp [solve, solve_postcond, CountEligible_nonneg, CountEligible_le_length]
-- </vc-theorems>
