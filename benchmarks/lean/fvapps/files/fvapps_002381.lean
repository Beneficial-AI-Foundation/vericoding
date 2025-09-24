-- <vc-preamble>
def isOdd (n : Int) : Bool :=
  n % 2 = 1

/- Helper function to test if a number is even -/

def isEven (n : Int) : Bool :=
  n % 2 = 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def threeConsecutiveOdds (arr : List Int) : Bool := sorry

theorem threeConsecutiveOdds_returns_bool (arr : List Int) :
  threeConsecutiveOdds arr = true ∨ threeConsecutiveOdds arr = false :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem threeConsecutiveOdds_true_implies_consecutive (arr : List Int) :
  threeConsecutiveOdds arr = true →
  ∃ i, i + 2 < arr.length ∧
       isOdd arr[i]! ∧ isOdd arr[i+1]! ∧ isOdd arr[i+2]! :=
sorry

theorem threeConsecutiveOdds_false_implies_no_consecutive (arr : List Int) :
  threeConsecutiveOdds arr = false →
  ∀ i, i + 2 < arr.length →
      ¬(isOdd arr[i]! ∧ isOdd arr[i+1]! ∧ isOdd arr[i+2]!) :=
sorry

theorem all_odds_returns_true {arr : List Int} (h : arr.length ≥ 3)
  (h₂ : ∀ x ∈ arr, isOdd x) :
  threeConsecutiveOdds arr = true :=
sorry

theorem all_evens_returns_false {arr : List Int}
  (h : ∀ x ∈ arr, isEven x) :
  threeConsecutiveOdds arr = false :=
sorry
-- </vc-theorems>