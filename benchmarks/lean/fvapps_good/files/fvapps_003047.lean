-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def listOfNumsInBounds (start : Nat) (end_ : Nat) : List Nat := sorry

theorem listOfNumsInBounds_length (start : Nat) (end_ : Nat) :
  (listOfNumsInBounds start end_).length = end_ - start + 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem listOfNumsInBounds_starts_with_start (start : Nat) (end_ : Nat) :
  start ≤ end_ →
  (listOfNumsInBounds start end_).head! = start := sorry

theorem listOfNumsInBounds_within_bounds (start : Nat) (end_ : Nat) (n : Nat) :
  start ≤ end_ →
  n ∈ (listOfNumsInBounds start end_) →
  start ≤ n ∧ n ≤ end_ := sorry

theorem listOfNumsInBounds_all_included (start : Nat) (end_ : Nat) (n : Nat) :
  start ≤ end_ →
  start ≤ n →
  n ≤ end_ →
  n ∈ (listOfNumsInBounds start end_) := sorry
-- </vc-theorems>