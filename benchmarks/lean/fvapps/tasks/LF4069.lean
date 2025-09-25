-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def string_clean (s : String) : String := sorry

-- Main properties of string_clean
-- </vc-definitions>

-- <vc-theorems>
theorem string_clean_properties (s : String) :
  let result := string_clean s
  -- No digits in result
  (∀ c ∈ result.data, !c.isDigit) ∧
  -- Maintains relative order of non-digits
  (result = String.mk (s.data.filter (fun c => !c.isDigit))) ∧ 
  -- Result length ≤ original length
  (result.length ≤ s.length) := sorry

-- String with only letters remains unchanged

theorem string_clean_only_letters (s : String) :
  (∀ c ∈ s.data, c.isAlpha) →
  string_clean s = s := sorry

-- String with only digits returns empty string 

theorem string_clean_only_digits (s : String) :
  (∀ c ∈ s.data, c.isDigit) →
  string_clean s = "" := sorry
-- </vc-theorems>