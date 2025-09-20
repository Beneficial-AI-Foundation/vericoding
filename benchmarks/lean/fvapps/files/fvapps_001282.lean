-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calcMinOpsLuckyNum (n : String) : Nat :=
  sorry

def countNonLuckyDigits (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_nonnegative (n : String) :
  calcMinOpsLuckyNum n ≥ 0 :=
sorry

theorem max_ops_is_length (n : String) :
  calcMinOpsLuckyNum n ≤ n.length :=
sorry

theorem ops_equals_non_lucky_digits (n : String) :
  calcMinOpsLuckyNum n = countNonLuckyDigits n :=
sorry
-- </vc-theorems>