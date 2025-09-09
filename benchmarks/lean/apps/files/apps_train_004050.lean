def StringMatches (pattern str : String) : Bool :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def shorten_to_date (s : String) : String :=
sorry

theorem shorten_to_date_property (dateString : String) :
  (dateString.contains ',' : Bool) ∧ 
  (StringMatches "[A-Za-z]+ [A-Za-z]+ \\d+, \\d+(?:am|pm)" dateString) →
  let result := shorten_to_date dateString
  ¬(result.contains ',' : Bool) ∧
  result = (dateString.splitOn ",").get! 0 ∧ 
  result.length < dateString.length :=
sorry

theorem shorten_to_date_requires_comma (s : String) :
  ¬((s.contains ',' : Bool) ∧ (s.splitOn ",").length = 2) →
  False :=
sorry

/-
info: 'Friday May 2'
-/
-- #guard_msgs in
-- #eval shorten_to_date "Friday May 2, 7pm"

/-
info: 'Tuesday January 29'
-/
-- #guard_msgs in
-- #eval shorten_to_date "Tuesday January 29, 10pm"

/-
info: 'Wed September 1'
-/
-- #guard_msgs in
-- #eval shorten_to_date "Wed September 1, 3am"

-- Apps difficulty: introductory
-- Assurance level: unguarded