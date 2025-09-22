-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hex_to_dec (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dec_to_hex_to_dec_roundtrip (n : Nat) :
  hex_to_dec (String.mk (Nat.toDigits 16 n)) = n :=
sorry

theorem invalid_hex_raises (s : String)
  (h : ∃ c ∈ s.data, c ∉ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f', 'A', 'B', 'C', 'D', 'E', 'F']) :
  hex_to_dec s = 0 :=
sorry
-- </vc-theorems>