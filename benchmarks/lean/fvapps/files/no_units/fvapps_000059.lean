-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_array_differences (n : Nat) (arr : List Int) : Int × Int := sorry

/- Properties for all-negative-ones case -/
-- </vc-definitions>

-- <vc-theorems>
theorem all_neg_ones_result {n : Nat} {arr : List Int} 
  (h : ∀ x ∈ arr, x = -1) :
  solve_array_differences n arr = (0, 0) := sorry
-- </vc-theorems>