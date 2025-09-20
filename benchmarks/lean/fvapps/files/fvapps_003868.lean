-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encode (s : String) : String := sorry

theorem encode_case_insensitive (s : String) : 
  encode s.toUpper = encode s.toLower := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encode_produces_only_digits (s : String) (p : String.Pos) :
  ((encode s).get p).isDigit := sorry

theorem encode_length_consistency (s : String) :
  (encode s).length = s.data.foldl (fun acc c => acc + (toString (c.toUpper.toNat - 64)).length) 0 := sorry

theorem encode_single_letter (c : Char) :
  encode (String.mk [c]) = toString (c.toUpper.toNat - 64) := sorry
-- </vc-theorems>