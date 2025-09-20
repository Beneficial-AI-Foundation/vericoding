-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def clean_binary_string (n : Nat) (s : String) : String :=
sorry

def string_of_zeros (n : Nat) : String :=
sorry

def string_of_ones (n : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem clean_preserves_all_zeros (n : Nat) :
  clean_binary_string n (string_of_zeros n) = string_of_zeros n :=
sorry

theorem clean_preserves_all_ones (n : Nat) :
  clean_binary_string n (string_of_ones n) = string_of_ones n :=
sorry

theorem clean_preserves_monotonic_transitions (n : Nat) (s : String) :
  s = "0001" ∨ s = "0011" ∨ s = "0111" → clean_binary_string n s = s :=
sorry

theorem clean_shortens_alternating (n : Nat) :
  clean_binary_string 4 "0101" = "001" :=
sorry

theorem clean_shortens_complex_pattern (n : Nat) :
  clean_binary_string 8 "11001101" = "01" :=
sorry

theorem clean_reduces_to_minimal (n : Nat) :
  clean_binary_string 6 "100110" = "0" :=
sorry
-- </vc-theorems>