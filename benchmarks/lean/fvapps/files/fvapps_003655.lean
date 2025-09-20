-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def spacify (s : String) : String := sorry

theorem spacify_length (s : String) :
  let result := spacify s
  if s = "" then
    result = ""
  else
    result.length = s.length * 2 - 1
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem spacify_chars_preserved (s : String) :
  String.join ((spacify s).splitOn " ") = s := sorry

theorem spacify_spaces_between (s : String) (h : s.length > 1) :
  ∀ i, i < (spacify s).length → 
  i % 2 = 1 → ((spacify s).data.get ⟨i, by sorry⟩) = ' ' := sorry
-- </vc-theorems>