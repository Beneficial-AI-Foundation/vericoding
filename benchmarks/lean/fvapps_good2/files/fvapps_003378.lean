-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countInversion (s : List Int) : Nat :=
sorry

def isSorted (s : List Int) : Bool :=
sorry

def isAntiSorted (s : List Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem countInversion_nonnegative (s : List Int) :
  countInversion s ≥ 0 :=
sorry

theorem countInversion_sorted_zero (s : List Int) :
  isSorted s = true → countInversion s = 0 :=
sorry

theorem countInversion_reverse_sorted_max (s : List Int) :
  let maxInv := s.length * (s.length - 1) / 2
  isAntiSorted s = true → countInversion s ≤ maxInv :=
sorry

theorem countInversion_small_seq (s : List Int) :
  s.length ≤ 1 → countInversion s = 0 :=
sorry
-- </vc-theorems>