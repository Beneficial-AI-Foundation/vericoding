-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digitSum (n : Nat) : Nat :=
  sorry

def isDivisibleByDigitSum (n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isDivisibleByDigitSum_spec (n : Nat) (h : n > 0) :
  let ds := digitSum n
  isDivisibleByDigitSum n = "Yes" ↔ n % ds = 0
  :=
sorry

theorem isDivisibleByDigitSum_returns_valid_result (n : Nat) (h : n > 0) :
  isDivisibleByDigitSum n = "Yes" ∨ isDivisibleByDigitSum n = "No"
  :=
sorry
-- </vc-theorems>