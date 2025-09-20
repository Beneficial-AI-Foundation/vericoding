-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_isogram (s : String) : Bool := sorry

theorem empty_and_single_chars_are_isograms (s : String) :
  s.length ≤ 1 → is_isogram s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem repeated_chars_not_isogram (s : String) :
  s.length > 0 → ¬(is_isogram (s ++ String.mk [s.get 0])) := sorry

theorem all_unique_chars_is_isogram (s : String) :
  let unique_chars := String.mk (List.eraseDups s.data)
  is_isogram unique_chars := sorry
-- </vc-theorems>