-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def okkOokOo (s : String) : String :=
  sorry

/- The function correctly encodes basic ASCII characters -/
-- </vc-definitions>

-- <vc-theorems>
theorem basic_ascii_encoding (input : String) :
  okkOokOo "Ok, Ook, Ooo!" = "H" :=
sorry

/- The function handles multiple characters correctly -/

theorem multiple_char_encoding :
  okkOokOo "Ok, Ook, Ooo?Okk, Ook, Ok" = "He" :=
sorry

/- The length of output matches the number of separators plus one -/

theorem length_matches_separators :
  String.length (okkOokOo "Ok, Ook, Ooo?Okk, Ook, Ok") = 2 :=
sorry

/- The output only contains printable ASCII characters -/

theorem output_is_printable_ascii (s : String) (c : Char) :
  c ∈ (okkOokOo s).data →
  32 ≤ c.toNat ∧ c.toNat ≤ 126 :=
sorry

/-
info: 'H'
-/
-- #guard_msgs in
-- #eval okkOokOo "Ok, Ook, Ooo!"

/-
info: 'Hello'
-/
-- #guard_msgs in
-- #eval okkOokOo "Ok, Ook, Ooo?  Okk, Ook, Ok?  Okk, Okk, Oo?  Okk, Okk, Oo?  Okk, Okkkk!"

/-
info: 'World!'
-/
-- #guard_msgs in
-- #eval okkOokOo "Ok, Ok, Okkk?  Okk, Okkkk?  Okkk, Ook, O?  Okk, Okk, Oo?  Okk, Ook, Oo?  Ook, Ooook!"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded