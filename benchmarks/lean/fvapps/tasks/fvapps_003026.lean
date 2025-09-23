-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def total_bill (s : String) : Nat :=
  sorry

def countChar (s : String) (c : Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem total_bill_nonnegative (s : String) :
  total_bill s ≥ 0 :=
sorry

theorem total_bill_even (s : String) :
  total_bill s % 2 = 0 :=
sorry

theorem total_bill_spaces (s : String) :
  total_bill s = total_bill (s.replace " " "") :=
sorry

theorem total_bill_repeated (n : Nat) (s : String) :
  s = String.mk (List.replicate n 'r') →
  total_bill s = 2 * (n - n/5) :=
sorry
-- </vc-theorems>