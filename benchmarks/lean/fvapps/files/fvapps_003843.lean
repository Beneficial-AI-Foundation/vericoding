-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def acronym_buster (s : String) : String := sorry

theorem output_is_always_string (s : String) :
  ∃ (result : String), acronym_buster s = result := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem known_acronyms_not_in_splits (s : String) (acronym : String) :
  acronym ∈ ["KPI", "EOD", "EOP", "TBD", "WAH", "IAM", "OOO", "NRN", "CTA", "SWOT"] →
  ¬(acronym_buster s).contains (Char.ofNat 65) →  -- placeholder since String.contains expects Char
  acronym ∉ (acronym_buster s).splitOn " " := by sorry

theorem basic_acronym_replacement :
  ∃ (result : String), 
    result = (acronym_buster "EOD").toLower ∧ 
    (∀ c ∈ "the end of the day".data, result.contains c) := by sorry
-- </vc-theorems>