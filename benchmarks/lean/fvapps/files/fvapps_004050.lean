-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def StringMatches (pattern str : String) : Bool :=
sorry

def shorten_to_date (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>