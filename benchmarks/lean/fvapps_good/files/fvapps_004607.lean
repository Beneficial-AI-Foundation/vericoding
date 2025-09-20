-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def travel (r : String) (zipcode : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem travel_empty_zipcode (addrs : String) :
  travel addrs "" = ":/" := by sorry

theorem travel_invalid_zipcode (addrs : String) (zip : String) :
  zip = "AB 123" →
  travel addrs zip = "AB 123:/" := by sorry

theorem travel_valid_zipcode_format (addrs : String) (stateZip : String) :
  addrs ≠ "" →
  let result := travel addrs stateZip
  result.startsWith s!"{stateZip}:" ∧
  result.contains '/' := by sorry

theorem travel_valid_result_components (addrs : String) (stateZip : String) 
    (result : String) (h : result = travel addrs stateZip) :
  result ≠ s!"{stateZip}:/" →
  let components := result.split (· == '/')
  let streets := ((components.get? 0).getD "").split (· == ':')
  let numbers := (components.get? 1).getD ""
  (∀ n ∈ (numbers.split (· == ',')), n.all Char.isDigit) ∧
  (∀ s ∈ ((streets.get? 1).getD "").split (· == ','), s.all (fun c => c.isAlpha ∨ c == ' ')) := by sorry

theorem travel_malformed_input (badInput : String) :
  let result := travel badInput "ST 12345"
  result = "ST 12345:/" ∨
  (result.startsWith "ST 12345:" ∧ result.contains '/') := by sorry
-- </vc-theorems>