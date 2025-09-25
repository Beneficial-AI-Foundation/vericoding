-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_correct_characters (s1 s2 : String) : Nat := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem different_length_strings_raise_error {s1 s2 : String} : 
  s1.length ≠ s2.length → count_correct_characters s1 s2 = 0 := 
  sorry

theorem identical_strings_return_length {s : String} :
  count_correct_characters s s = s.length := 
  sorry

theorem result_cannot_exceed_length {s1 s2 : String} :
  s1.length = s2.length → count_correct_characters s1 s2 ≤ s1.length :=
  sorry

theorem result_is_symmetric {s1 s2 : String} :
  s1.length = s2.length → count_correct_characters s1 s2 = count_correct_characters s2 s1 :=
  sorry

theorem result_is_nonnegative {s1 s2 : String} :
  s1.length = s2.length → count_correct_characters s1 s2 ≥ 0 := 
  sorry
-- </vc-theorems>