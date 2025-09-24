-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def how_many_dalmatians (n: Int) : String := sorry

theorem dalmatians_output_is_valid_string (n: Int) :
  how_many_dalmatians n = "Hardly any" ∨
  how_many_dalmatians n = "More than a handful!" ∨
  how_many_dalmatians n = "Woah that's a lot of dogs!" ∨
  how_many_dalmatians n = "101 DALMATIONS!!!" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem small_numbers_get_hardly_any (n: Int) :
  n ≤ 10 → how_many_dalmatians n = "Hardly any" := sorry

theorem medium_numbers_get_handful (n: Int) :
  11 ≤ n ∧ n ≤ 50 → how_many_dalmatians n = "More than a handful!" := sorry

theorem large_numbers_get_lots (n: Int) :
  (51 ≤ n ∧ n ≤ 100) ∨ 102 ≤ n →
  how_many_dalmatians n = "Woah that's a lot of dogs!" := sorry

theorem exactly_101 :
  how_many_dalmatians 101 = "101 DALMATIONS!!!" := sorry
-- </vc-theorems>