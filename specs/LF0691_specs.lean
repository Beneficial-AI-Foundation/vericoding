-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxval (arr : List Int) : Int := sorry

theorem maxval_finite (arr : List Int) (h : arr.length ≥ 4) :
  ∃ n : Int, maxval arr = n := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxval_same_elements (arr : List Int) (h1 : arr.length ≥ 4) 
    (h2 : ∀ (x : Int), x ∈ arr → x = arr.getD 0 0) :
  maxval arr = 0 := by sorry

theorem maxval_bounded (arr : List Int) (h : arr.length ≥ 4) :
  let maxVal := arr.getD 0 0 
  let minVal := arr.getD 0 0
  let maxPossible := 2 * max (maxVal - minVal) (maxVal + minVal)
  maxval arr ≤ maxPossible ∧ maxval arr ≥ -maxPossible := by sorry
-- </vc-theorems>