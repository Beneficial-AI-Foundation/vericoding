-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_count (s : String := "") : Count :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_count_nonnegative (s : String) :
  let result := get_count s
  result.vowels ≥ 0 ∧ result.consonants ≥ 0 :=
  sorry

theorem get_count_sum_equals_letters (s : String) :
  let result := get_count s
  let letter_count := (s.data.filter Char.isAlpha).length
  result.vowels + result.consonants = letter_count :=
  sorry
-- </vc-theorems>