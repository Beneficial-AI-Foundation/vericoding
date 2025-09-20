-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def delete_digit (n : Nat) : Nat :=
  sorry

def stringToNat (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem delete_digit_length (n : Nat) (h : n ≥ 10) :
  (toString (delete_digit n)).length = (toString n).length - 1 :=
sorry

theorem delete_digit_smaller (n : Nat) (h : n ≥ 10) :
  delete_digit n < n :=
sorry

theorem delete_digit_natural (n : Nat) (h : n ≥ 10) :
  delete_digit n ≥ 0 :=
sorry
-- </vc-theorems>