-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decompose : Int → List Nat × Int := sorry

/- Decompose function's list result contains only numbers greater than 1 -/
-- </vc-definitions>

-- <vc-theorems>
theorem decompose_result_gt_one (n : Int) :
  let (result, _) := decompose n
  ∀ k ∈ result, k > 1 := sorry
-- </vc-theorems>