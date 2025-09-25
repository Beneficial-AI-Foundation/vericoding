-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumDigits (n : Nat) : Nat :=
sorry

def isAscending (n : Nat) : Bool :=
sorry

def numDigits (n : Nat) : Nat :=
sorry

def find_all (sumDig digs : Nat) : Option (Nat × Nat × Nat) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_for_impossible_sums (sumDig digs : Nat) :
  (sumDig > 9 * digs ∨ sumDig < digs) → find_all sumDig digs = none :=
sorry

theorem valid_output_format {sumDig digs : Nat} (res : Nat × Nat × Nat) :
  find_all sumDig digs = some res →
  let (count, first, last) := res
  count > 0 ∧
  numDigits first = digs ∧
  numDigits last = digs ∧
  first ≤ last :=
sorry

theorem solutions_have_correct_sum {sumDig digs : Nat} (res : Nat × Nat × Nat) :
  find_all sumDig digs = some res →
  let (_, first, last) := res
  sumDigits first = sumDig ∧
  sumDigits last = sumDig :=
sorry

theorem solutions_are_ascending {sumDig digs : Nat} (res : Nat × Nat × Nat) :
  find_all sumDig digs = some res →
  let (_, first, last) := res
  isAscending first ∧
  isAscending last :=
sorry
-- </vc-theorems>