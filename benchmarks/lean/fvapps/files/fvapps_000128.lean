-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.repeat (s : String) (n : Nat) : String :=
  sorry

def number_of_arrays (s : String) (k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_digit_valid {d : Char} {k : Nat}
  (h1 : d ∈ ['1', '2', '3', '4', '5', '6', '7', '8', '9'])
  (h2 : k > 0)
  : number_of_arrays (String.mk [d]) k = if (d.toNat - 48) ≤ k then 1 else 0 :=
sorry

theorem single_zero_invalid {k : Nat} (h : k > 0)
  : number_of_arrays "0" k = 0 :=
sorry
-- </vc-theorems>