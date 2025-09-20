-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def num_good_splits (s : String) : Nat :=
sorry

def reverse (s : String) : String :=
sorry

def uniqueChars (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem num_good_splits_bounds (s : String) (h : s.length > 0) :
  num_good_splits s ≤ s.length - 1 ∧ num_good_splits s ≥ 0 :=
sorry
-- </vc-theorems>