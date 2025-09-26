-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_vowels (s : String) : Option Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_vowels_eq_vowels_count (s : String) :
  count_vowels s = some (s.data.filter (fun c => ['a', 'e', 'i', 'o', 'u'].contains c.toLower)).length := by
  sorry

theorem count_vowels_case_insensitive (s : String) :
  count_vowels s.toLower = count_vowels s.toUpper := by
  sorry

theorem count_vowels_empty :
  count_vowels "" = some 0 := by
  sorry
-- </vc-theorems>