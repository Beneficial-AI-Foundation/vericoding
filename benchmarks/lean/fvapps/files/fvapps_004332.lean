-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_consec_zeros (n: String) : String :=
  sorry

def toWord (n: Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_consec_zeros_valid_input {n: String} (h: ∃ (k: Nat), k > 0 ∧ k ≤ 10^6 ∧ n = toString k) :
  let result := max_consec_zeros n
  ∃ word, word ∈ ["Zero", "One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine",
                  "Ten", "Eleven", "Twelve", "Thirteen"] ∧ result = word :=
sorry

theorem powers_of_two_zeros {n: Nat} (h: n > 0 ∧ n ≤ 12) :
  max_consec_zeros (toString (2^n)) = toWord (n-1) :=
sorry

theorem equivalent_decimal_values {n: Nat} (h: n > 0 ∧ n ≤ 10000) :
  max_consec_zeros (toString n) = max_consec_zeros (toString (n : Nat)) :=
sorry
-- </vc-theorems>