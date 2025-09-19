-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_char_count (s : String) : List (Nat × List Char) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_char_count_empty :
  get_char_count "" = [] := 
  sorry

theorem get_char_count_single (c : Char) :
  get_char_count (String.singleton c) = [(1, [c])] :=
  sorry

theorem get_char_count_duplicates :
  get_char_count "aaa" = [(3, ['a'])] :=
  sorry

theorem get_char_count_distinct :
  let res := get_char_count "abc"
  ∃ l, (1, l) ∈ res ∧ l = ['a', 'b', 'c'] :=
  sorry

theorem get_char_count_mixed :
  get_char_count "mississippi" = [(4, ['i', 's']), (2, ['p']), (1, ['m'])] :=
  sorry
-- </vc-theorems>