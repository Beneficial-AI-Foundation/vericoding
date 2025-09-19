-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def classify_quotes (quote : String) : String := sorry

def splitString (s : String) : List String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem classify_quotes_result_valid (quote : String) :
  classify_quotes quote = "Real Fancy" ∨ classify_quotes quote = "regularly fancy" := sorry

theorem classify_quotes_not_condition (quote : String) :
  classify_quotes quote = (if (splitString quote).contains "not" then "Real Fancy" else "regularly fancy") := sorry

theorem classify_quotes_regular (quote : String) :
  ¬(splitString quote).contains "not" → classify_quotes quote = "regularly fancy" := sorry

theorem classify_quotes_all_not (n : Nat) (h : n > 0) :
  classify_quotes (String.join (List.replicate n "not" |>.intersperse " ")) = "Real Fancy" := sorry
-- </vc-theorems>