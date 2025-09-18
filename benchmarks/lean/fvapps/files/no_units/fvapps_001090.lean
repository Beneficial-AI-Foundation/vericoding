-- <vc-preamble>
def isValidNamePart (s: String) : Bool :=
  sorry

def formatName (input: List String) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def formatNameStr (input: String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem format_name_list_properties {parts: List String} 
  (h: ∃ p ∈ parts, isValidNamePart p = true) :
  let result := formatName parts
  let resultParts := result.split (· = ' ')
  -- Result is a string
  result.length ≥ 0 ∧  
  -- Last part is capitalized original
  resultParts.getLast! = (parts.getLast!).capitalize ∧
  -- Other parts are initials
  (parts.length > 1 → 
    ∀ i < parts.length - 1,
    resultParts[i]! = s!"{(parts[i]!).get 0}.") :=
  sorry

theorem format_name_string_properties {input: String}
  (h: ∃ c ∈ input.data, c.isAlpha) :
  let validParts := (input.split (· = ' ')).filter isValidNamePart
  let result := formatNameStr input
  let resultParts := result.split (· = ' ')
  (validParts.length > 0) →
  -- Result is a string
  result.length ≥ 0 ∧
  -- Parts lengths match
  resultParts.length = validParts.length ∧
  -- Initials format
  (validParts.length > 1 →
    ∀ i < validParts.length - 1,
    (resultParts[i]!).endsWith "." ∧
    (resultParts[i]!).length = 2) ∧
  -- Last name is starts with uppercase
  (resultParts.getLast!).get 0 ≥ 'A' ∧ 
  (resultParts.getLast!).get 0 ≤ 'Z' :=
  sorry
-- </vc-theorems>