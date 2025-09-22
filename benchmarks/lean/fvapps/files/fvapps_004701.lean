-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def meeting (input : String) : Option String := sorry

theorem meeting_single_name_transformation {name first last : String}
  (h : name = first ++ ":" ++ last) :
  meeting name = some ("(" ++ last.toUpper ++ ", " ++ first.toUpper ++ ")") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem meeting_invalid_format_no_colon (s : String) 
  (h : ¬ s.contains ':') : 
  meeting s = none := sorry

theorem meeting_invalid_format_multiple_colons (s : String)
  (h : (s.splitOn ":").length > 2) :
  meeting s = none := sorry
-- </vc-theorems>