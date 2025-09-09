-- <vc-helpers>
-- </vc-helpers>

def meeting (input : String) : Option String := sorry

theorem meeting_single_name_transformation {name first last : String}
  (h : name = first ++ ":" ++ last) :
  meeting name = some ("(" ++ last.toUpper ++ ", " ++ first.toUpper ++ ")") := sorry

theorem meeting_invalid_format_no_colon (s : String) 
  (h : ¬ s.contains ':') : 
  meeting s = none := sorry

theorem meeting_invalid_format_multiple_colons (s : String)
  (h : (s.splitOn ":").length > 2) :
  meeting s = none := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval meeting "Fred:Corwill;Wilfred:Corwill;Barney:Tornbull;Betty:Tornbull;Bjon:Tornbull;Raphael:Corwill;Alfred:Corwill"

/-
info: expected2
-/
-- #guard_msgs in
-- #eval meeting "Alex:Gates;Bill:Gates;Steve:Jobs"

/-
info: expected3
-/
-- #guard_msgs in
-- #eval meeting "John:Smith;Jane:Smith;Joe:Brown"

-- Apps difficulty: introductory
-- Assurance level: unguarded