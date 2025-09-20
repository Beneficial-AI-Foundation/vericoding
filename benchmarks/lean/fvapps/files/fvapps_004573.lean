-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def okkOokOo (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem basic_ascii_encoding (input : String) :
  okkOokOo "Ok, Ook, Ooo!" = "H" :=
sorry

theorem multiple_char_encoding :
  okkOokOo "Ok, Ook, Ooo?Okk, Ook, Ok" = "He" :=
sorry

theorem length_matches_separators :
  String.length (okkOokOo "Ok, Ook, Ooo?Okk, Ook, Ok") = 2 :=
sorry

theorem output_is_printable_ascii (s : String) (c : Char) :
  c ∈ (okkOokOo s).data →
  32 ≤ c.toNat ∧ c.toNat ≤ 126 :=
sorry
-- </vc-theorems>