-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_country_codes (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_country_codes_non_negative (s : String) :
  count_country_codes s ≥ 0 := sorry

theorem count_country_codes_bounded_by_substrings (s : String) :
  count_country_codes s ≤ s.length - 1 := sorry

theorem count_country_codes_bounded_by_unique_pairs (s : String) :
  let unique_chars := (s.toList.eraseDups).length
  count_country_codes s ≤ unique_chars * unique_chars := sorry

theorem count_country_codes_repeated_char (c : Char) (n : Nat) :
  n ≥ 2 →
  count_country_codes (String.mk (List.replicate n c)) = 1 := sorry

theorem count_country_codes_empty :
  count_country_codes "" = 0 := sorry

theorem count_country_codes_single_char :
  ∀ c : Char, count_country_codes (String.mk [c]) = 0 := sorry
-- </vc-theorems>